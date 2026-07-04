import Body.Chunked

/-!
# Correctness of chunked transfer decoding (RFC 9112 §7.1)

`Body/Chunked.lean` establishes *safety* facts about the chunk decoder — the
header parse is total and consumed-monotone, a decoded chunk is in-bounds, and
the streaming fold terminates. Those say the decoder never runs off the buffer
and always makes progress. They do **not** say the decoder returns the *right*
bytes.

This file upgrades that to a *correctness* claim: the decoder's output MATCHES
what the RFC dictates. RFC 9112 §7.1 gives the wire grammar

    chunked-body = *chunk last-chunk trailer-section CRLF
    chunk        = chunk-size [ chunk-ext ] CRLF chunk-data CRLF
    chunk-size   = 1*HEXDIG
    last-chunk   = 1*("0") [ chunk-ext ] CRLF
    chunk-data   = 1*OCTET

and mandates that the decoded message body is the **concatenation of the
chunk-data fields, each carrying exactly its declared chunk-size octets**, with
none of the framing octets (size digits, CRLFs, the terminal) appearing in the
body.

We model the subset the decoder implements — the same subset `Body/Chunked.lean`
documents as in scope: no `chunk-ext`, no trailer fields, and the terminal is the
bare `0 CRLF CRLF`. Within that subset the specification below is written *from
the grammar*, independently of the decoder.

## The specification (independent of the decoder)

`IsChunking encoded plain` is an inductive relation asserting that the octet
string `encoded` is a valid chunked encoding of the payload `plain`, read
straight off the RFC grammar:

* `terminal` — a size line of hex digits denoting `0`, then `CRLF CRLF`, encodes
  the empty payload.
* `chunk` — a size line of hex digits denoting `k > 0`, then `CRLF`, then exactly
  `k` data octets, then `CRLF`, followed by an encoding of `rest`, encodes
  `data ++ rest`.

Crucially the relation refers only to the *value* semantics of a hex digit run
(`parseHex`, the RFC's `chunk-size = 1*HEXDIG` reading) and the framing octets
`CR`/`LF`. It never mentions `decodeStream`, `decodeFrame`, or `parseHeader`: it
is not the decoder renamed. It describes, declaratively, which byte strings are
legal chunkings of which payloads. A *wrong* decoder that dropped a chunk or
mis-counted a chunk-size would deliver a `plain` this relation does not hold of,
and would therefore fail the theorem below.

## The refinement theorem

`dechunk` is the decoder viewed as a payload extractor: run the streaming decode
and, on a `complete` result that consumed the *whole* input, return the delivered
body.

    dechunk_iff_spec : dechunk encoded = some plain ↔ IsChunking encoded plain

Left-to-right is *soundness*: whenever the real decoder accepts `encoded` and
hands back `plain`, `encoded` genuinely is a chunking of `plain` — the decoder
invents nothing and drops nothing. Right-to-left is *completeness*: every string
the grammar calls a chunking of `plain` is decoded, to exactly `plain`. Together:
`dechunk` recovers EXACTLY the concatenated payload, neither more nor less.
-/

namespace Body
namespace Chunked

open Body.Hex

/-! ## The RFC-behavior specification -/

/-- `IsChunking encoded plain`: `encoded` is a valid chunked encoding whose
decoded body is `plain`. Written directly from the RFC 9112 §7.1 grammar (the
no-`chunk-ext`, no-trailer subset the decoder models), independently of the
decoder. -/
inductive IsChunking : Bytes → Bytes → Prop where
  /-- The terminal `last-chunk`: a hex size line denoting `0`, then `CRLF CRLF`.
  Decodes the empty payload. -/
  | terminal (digits : Bytes)
      (hdig : ∀ b ∈ digits, b ≠ CR)
      (hz : parseHex digits = some 0) :
      IsChunking (digits ++ CR :: LF :: CR :: LF :: []) []
  /-- A data chunk: a hex size line denoting `k = data.length > 0`, then `CRLF`,
  then exactly `k` data octets, then `CRLF`, then an encoding of `rest`. -/
  | chunk (digits data restEnc restPlain : Bytes)
      (hdig : ∀ b ∈ digits, b ≠ CR)
      (hsz : parseHex digits = some data.length)
      (hle : data.length ≤ maxChunkSize)
      (hpos : data ≠ [])
      (h : IsChunking restEnc restPlain) :
      IsChunking (digits ++ CR :: LF :: data ++ CR :: LF :: restEnc) (data ++ restPlain)

/-! ## The decoder as a payload extractor -/

/-- The chunk decoder viewed as `Bytes → Option Bytes`: run `decodeStream`; on a
`complete` result that consumed the entire input, return the delivered body;
otherwise fail. (Requiring full consumption rejects trailing octets after the
terminal chunk, matching the RFC's "the body ends at the last-chunk".) -/
def dechunk (buf : Bytes) : Option Bytes :=
  match decodeStream buf with
  | .complete body consumed => if consumed = buf.length then some body else none
  | _ => none

/-! ## Framing helpers -/

/-- `parseHexAux` only succeeds on a run of hex digits, and `CR` (`0x0D`) is not a
hex digit — so a parsable run contains no `CR`. -/
theorem parseHexAux_no_cr (acc : Nat) (bs : Bytes) (v : Nat)
    (h : parseHexAux acc bs = some v) : ∀ b ∈ bs, b ≠ CR := by
  induction bs generalizing acc with
  | nil => intro b hb; simp at hb
  | cons x xs ih =>
    intro b hb hbcr
    simp only [parseHexAux] at h
    cases hx : hexVal x with
    | none => rw [hx] at h; simp at h
    | some d =>
      rw [hx] at h; simp only [Option.some_bind] at h
      rcases List.mem_cons.mp hb with heq | hb'
      · subst hbcr; rw [← heq] at hx
        rw [show hexVal CR = none from by decide] at hx; simp at hx
      · exact ih (acc * 16 + d) h b hb' hbcr

/-- `parseHex` only succeeds on a run of hex digits, none of which is `CR`. -/
theorem parseHex_no_cr (bs : Bytes) (v : Nat) (h : parseHex bs = some v) :
    ∀ b ∈ bs, b ≠ CR := by
  unfold parseHex at h
  cases hemp : bs.isEmpty with
  | true => rw [hemp] at h; simp at h
  | false =>
    rw [hemp] at h; simp only [Bool.false_eq_true, if_false] at h
    exact parseHexAux_no_cr 0 bs v h

/-- If `findCrlf buf = some p`, then the buffer, from offset `p`, is `CR LF`
followed by the remainder. -/
theorem findCrlf_drop (buf : Bytes) (p : Nat) (h : findCrlf buf = some p) :
    buf.drop p = CR :: LF :: buf.drop (p + 2) := by
  induction buf using findCrlf.induct generalizing p with
  | case1 a b rest hcond =>
    simp only [findCrlf, if_pos hcond, Option.some.injEq] at h
    subst h
    obtain ⟨rfl, rfl⟩ := hcond
    simp
  | case2 a b rest hcond ih =>
    simp only [findCrlf, if_neg hcond] at h
    cases hfc : findCrlf (b :: rest) with
    | none => rw [hfc] at h; simp at h
    | some q =>
      rw [hfc] at h; simp only [Option.map_some', Option.some.injEq] at h
      subst h
      have hih := ih q hfc
      have e : q + 1 + 2 = (q + 2) + 1 := by omega
      rw [e, List.drop_succ_cons, List.drop_succ_cons]
      exact hih
  | case3 t hlt =>
    cases t with
    | nil => simp [findCrlf] at h
    | cons x xs =>
      cases xs with
      | nil => simp [findCrlf] at h
      | cons y ys => exact absurd rfl (hlt x y ys)

/-- If `l.take 2 = [a, b]`, then `l = a :: b :: l.drop 2`. -/
theorem take2_split {α} (l : List α) (a b : α) (h : l.take 2 = [a, b]) :
    l = a :: b :: l.drop 2 := by
  match l, h with
  | x :: y :: t, h => simp only [List.take_succ_cons, List.take_zero] at h; simp_all

/-- If the two octets at offset `k` are `a b`, then from offset `k` the buffer is
`a :: b :: (buffer from k+2)`. -/
theorem take2_split_drop (l : Bytes) (a b : UInt8) (k : Nat)
    (h : (l.drop k).take 2 = [a, b]) : l.drop k = a :: b :: l.drop (k + 2) := by
  have hx := take2_split (l.drop k) a b h
  rwa [List.drop_drop] at hx

/-! ## Header/frame parse, factored through a size line -/

/-- A frame whose size line `digits` (no `CR`) denotes a positive, in-range
`data.length`, followed by `CRLF`, the `data` octets, `CRLF`, and any tail,
decodes to exactly that data chunk. Generalizes `decodeFrame_encodeChunk` from
the canonical `toHex` encoding to an arbitrary hex size line. -/
theorem decodeFrame_chunk_gen (digits data tail : Bytes)
    (hdig : ∀ b ∈ digits, b ≠ CR)
    (hsz : parseHex digits = some data.length)
    (hle : data.length ≤ maxChunkSize)
    (hpos : data ≠ []) :
    decodeFrame (digits ++ CR :: LF :: data ++ CR :: LF :: tail)
      = .chunk data (digits.length + data.length + 4) := by
  have hph : parseHeader (digits ++ CR :: LF :: data ++ CR :: LF :: tail)
      = .ok data.length (digits.length + 2) := by
    have e : digits ++ CR :: LF :: data ++ CR :: LF :: tail
        = digits ++ CR :: LF :: (data ++ CR :: LF :: tail) := by
      simp [List.append_assoc]
    rw [e, parseHeader_line digits _ hdig]
    simp only [hsz]
    rw [if_neg (Nat.not_lt.mpr hle)]
  have gA : digits ++ CR :: LF :: data ++ CR :: LF :: tail
      = (digits ++ [CR, LF]) ++ (data ++ CR :: LF :: tail) := by
    simp [List.append_assoc]
  have gB : digits ++ CR :: LF :: data ++ CR :: LF :: tail
      = (digits ++ [CR, LF] ++ data) ++ (CR :: LF :: tail) := by
    simp [List.append_assoc]
  have lenA : (digits ++ [CR, LF]).length = digits.length + 2 := by
    simp [List.length_append]
  have lenB : (digits ++ [CR, LF] ++ data).length = digits.length + 2 + data.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hTakeHead :
      ((digits ++ CR :: LF :: data ++ CR :: LF :: tail).drop (digits.length + 2)).take data.length
        = data := by
    rw [gA, List.drop_left' lenA]; exact List.take_left' rfl
  have hTakeData :
      ((digits ++ CR :: LF :: data ++ CR :: LF :: tail).drop (digits.length + 2 + data.length)).take 2
        = [CR, LF] := by
    rw [gB, List.drop_left' lenB]; rfl
  have hpos' : ¬ data.length = 0 := by
    have := List.length_pos.mpr hpos; omega
  have hlen : (digits ++ CR :: LF :: data ++ CR :: LF :: tail).length
      = digits.length + 2 + data.length + 2 + tail.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hnotlt : ¬ (digits ++ CR :: LF :: data ++ CR :: LF :: tail).length
      < digits.length + 2 + data.length + 2 := by rw [hlen]; omega
  simp only [decodeFrame, hph]
  rw [if_neg hpos', if_neg hnotlt, if_pos hTakeData, hTakeHead]
  rw [show digits.length + 2 + data.length + 2 = digits.length + data.length + 4 from by omega]

/-- A frame whose size line `digits` (no `CR`) denotes `0`, followed by
`CRLF CRLF` and any tail, decodes to the terminal chunk. -/
theorem decodeFrame_terminal_gen (digits tail : Bytes)
    (hdig : ∀ b ∈ digits, b ≠ CR)
    (hz : parseHex digits = some 0) :
    decodeFrame (digits ++ CR :: LF :: CR :: LF :: tail)
      = .terminal (digits.length + 4) := by
  have hph : parseHeader (digits ++ CR :: LF :: CR :: LF :: tail)
      = .ok 0 (digits.length + 2) := by
    have e : digits ++ CR :: LF :: CR :: LF :: tail
        = digits ++ CR :: LF :: (CR :: LF :: tail) := rfl
    rw [e, parseHeader_line digits _ hdig]
    simp only [hz]
    rw [if_neg (show ¬ maxChunkSize < 0 from by omega)]
  have gA : digits ++ CR :: LF :: CR :: LF :: tail
      = (digits ++ [CR, LF]) ++ (CR :: LF :: tail) := by
    simp [List.append_assoc]
  have lenA : (digits ++ [CR, LF]).length = digits.length + 2 := by
    simp [List.length_append]
  have hdrop : ((digits ++ CR :: LF :: CR :: LF :: tail).drop (digits.length + 2)).take 2
      = [CR, LF] := by
    rw [gA, List.drop_left' lenA]; rfl
  simp only [decodeFrame, hph]
  rw [if_pos trivial, if_pos hdrop,
      show digits.length + 2 + 2 = digits.length + 4 from by omega]

/-! ## Completeness: every grammar-valid chunking decodes to its payload -/

/-- **Completeness.** If `encoded` is a chunking of `plain`, the streaming
decoder returns exactly `plain`, consuming the whole input. -/
theorem isChunking_decodeStream (encoded plain : Bytes) (h : IsChunking encoded plain) :
    decodeStream encoded = .complete plain encoded.length := by
  induction h with
  | terminal digits hdig hz =>
    have hdf : decodeFrame (digits ++ CR :: LF :: CR :: LF :: [])
        = .terminal (digits.length + 4) := decodeFrame_terminal_gen digits [] hdig hz
    have hlen : (digits ++ CR :: LF :: CR :: LF :: ([] : Bytes)).length = digits.length + 4 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    rw [decodeStream_terminal _ _ hdf, hlen]
  | chunk digits data restEnc restPlain hdig hsz hle hpos h ih =>
    have hdf : decodeFrame (digits ++ CR :: LF :: data ++ CR :: LF :: restEnc)
        = .chunk data (digits.length + data.length + 4) :=
      decodeFrame_chunk_gen digits data restEnc hdig hsz hle hpos
    have hdrop : (digits ++ CR :: LF :: data ++ CR :: LF :: restEnc).drop
        (digits.length + data.length + 4) = restEnc := by
      have e : digits ++ CR :: LF :: data ++ CR :: LF :: restEnc
          = (digits ++ [CR, LF] ++ data ++ [CR, LF]) ++ restEnc := by
        simp [List.append_assoc]
      have hl : (digits ++ [CR, LF] ++ data ++ [CR, LF]).length
          = digits.length + data.length + 4 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [e, List.drop_left' hl]
    rw [decodeStream_chunk _ data _ hdf, hdrop, ih]
    have hlen : (digits ++ CR :: LF :: data ++ CR :: LF :: restEnc).length
        = (digits.length + data.length + 4) + restEnc.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [hlen]

/-! ## Soundness: every accepted input is a grammar-valid chunking -/

/-- Invert `decodeFrame … = .terminal c`: the buffer starts with a size line
denoting `0`, then `CRLF CRLF`. -/
theorem decodeFrame_terminal_inv (buf : Bytes) (c : Nat) (h : decodeFrame buf = .terminal c) :
    ∃ digits, (∀ b ∈ digits, b ≠ CR) ∧ parseHex digits = some 0 ∧
      c = digits.length + 4 ∧ buf = digits ++ CR :: LF :: CR :: LF :: buf.drop c := by
  unfold decodeFrame at h
  split at h
  · simp at h
  · simp at h
  · rename_i size headerLen hph
    split at h
    · rename_i hz
      subst hz
      split at h
      · rename_i hcrlf
        simp only [Frame.terminal.injEq] at h
        unfold parseHeader at hph
        split at hph
        · simp at hph
        · rename_i p hfc
          split at hph
          · simp at hph
          · rename_i size' hpx
            split at hph
            · simp at hph
            · simp only [Hdr.ok.injEq] at hph
              obtain ⟨hsz', hhl⟩ := hph
              subst hhl
              have hbound := findCrlf_some_bound buf p hfc
              have hplen : (buf.take p).length = p := by rw [List.length_take]; omega
              have hpx0 : parseHex (buf.take p) = some 0 := hsz' ▸ hpx
              have hsplit1 : buf.drop p = CR :: LF :: buf.drop (p + 2) := findCrlf_drop buf p hfc
              have hcrlf2 : buf.drop (p + 2) = CR :: LF :: buf.drop (p + 2 + 2) :=
                take2_split_drop buf CR LF (p + 2) hcrlf
              refine ⟨buf.take p, parseHex_no_cr _ _ hpx0, hpx0, by omega, ?_⟩
              rw [show c = p + 2 + 2 from by omega, ← hcrlf2, ← hsplit1,
                  List.take_append_drop]
      · simp at h
    · rename_i hz
      split at h
      · simp at h
      · split at h <;> simp at h

/-- Invert `decodeFrame … = .chunk data c`: the buffer starts with a size line
denoting `data.length > 0`, then `CRLF`, the `data` octets, `CRLF`. -/
theorem decodeFrame_chunk_inv (buf data : Bytes) (c : Nat) (h : decodeFrame buf = .chunk data c) :
    ∃ digits, (∀ b ∈ digits, b ≠ CR) ∧ parseHex digits = some data.length ∧
      data.length ≤ maxChunkSize ∧ data ≠ [] ∧ c = digits.length + data.length + 4 ∧
      buf = digits ++ CR :: LF :: data ++ CR :: LF :: buf.drop c := by
  unfold decodeFrame at h
  split at h
  · simp at h
  · simp at h
  · rename_i size headerLen hph
    split at h
    · rename_i hz
      subst hz
      split at h <;> simp at h
    · rename_i hz
      split at h
      · simp at h
      · rename_i hlt
        split at h
        · rename_i hcrlf
          simp only [Frame.chunk.injEq] at h
          obtain ⟨hdata, hc⟩ := h
          unfold parseHeader at hph
          split at hph
          · simp at hph
          · rename_i p hfc
            split at hph
            · simp at hph
            · rename_i size' hpx
              split at hph
              · simp at hph
              · simp only [Hdr.ok.injEq] at hph
                obtain ⟨hsz', hhl⟩ := hph
                subst hsz'; subst hhl
                have hbound := findCrlf_some_bound buf p hfc
                have hplen : (buf.take p).length = p := by rw [List.length_take]; omega
                have hdlen : data.length = size' := by
                  rw [← hdata, List.length_take, List.length_drop]; omega
                have hsplit1 : buf.drop p = CR :: LF :: buf.drop (p + 2) := findCrlf_drop buf p hfc
                have hcrlf2 : buf.drop (p + 2 + size') = CR :: LF :: buf.drop (p + 2 + size' + 2) :=
                  take2_split_drop buf CR LF (p + 2 + size') hcrlf
                have hne : data ≠ [] := by
                  intro he; rw [he] at hdlen; simp at hdlen; omega
                refine ⟨buf.take p, parseHex_no_cr _ _ hpx, by rw [hpx, hdlen], by rw [hdlen]; omega,
                  hne, by omega, ?_⟩
                have hdataEq : buf.drop (p + 2) = data ++ buf.drop (p + 2 + size') := by
                  have h1 : buf.drop (p + 2)
                      = (buf.drop (p + 2)).take size' ++ (buf.drop (p + 2)).drop size' :=
                    (List.take_append_drop size' (buf.drop (p + 2))).symm
                  rw [hdata, List.drop_drop] at h1
                  exact h1
                rw [show c = p + 2 + size' + 2 from by omega, ← hcrlf2, List.append_assoc,
                    List.cons_append, List.cons_append, ← hdataEq, ← hsplit1, List.take_append_drop]
        · simp at h

/-- **Soundness.** If the streaming decoder returns `complete plain` having
consumed the whole input, then `encoded` really is a chunking of `plain`. Proved
by strong induction on the buffer length (each data chunk strictly shrinks it). -/
theorem decodeStream_sound (n : Nat) : ∀ (encoded plain : Bytes) (consumed : Nat),
    encoded.length = n → decodeStream encoded = .complete plain consumed →
    consumed = encoded.length → IsChunking encoded plain := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro encoded plain consumed hn hds hcons
    cases hdf : decodeFrame encoded with
    | incomplete => rw [decodeStream_incomplete encoded hdf] at hds; simp at hds
    | error =>
      rw [show decodeStream encoded = Decoded.error from by rw [decodeStream, hdf]] at hds
      simp at hds
    | terminal c =>
      rw [decodeStream_terminal encoded c hdf] at hds
      simp only [Decoded.complete.injEq] at hds
      obtain ⟨hpl, hcc⟩ := hds
      subst hpl
      obtain ⟨digits, hdig, hz, hcEq, hbuf⟩ := decodeFrame_terminal_inv encoded c hdf
      have hdropnil : encoded.drop c = [] := by
        apply List.drop_eq_nil_of_le; omega
      rw [hdropnil] at hbuf
      rw [hbuf]
      exact IsChunking.terminal digits hdig hz
    | chunk data c =>
      rw [decodeStream_chunk encoded data c hdf] at hds
      cases hinner : decodeStream (encoded.drop c) with
      | incomplete => rw [hinner] at hds; simp at hds
      | error => rw [hinner] at hds; simp at hds
      | complete body c' =>
        rw [hinner] at hds
        simp only [Decoded.complete.injEq] at hds
        obtain ⟨hpl, hc⟩ := hds
        subst hpl
        obtain ⟨digits, hdig, hsz, hle, hne, hcEq, hbuf⟩ := decodeFrame_chunk_inv encoded data c hdf
        have hcpos : 0 < c ∧ c ≤ encoded.length := decodeFrame_chunk_bound encoded data c hdf
        have htlen : (encoded.drop c).length = encoded.length - c := List.length_drop c encoded
        have hc'full : c' = (encoded.drop c).length := by omega
        have hlt : (encoded.drop c).length < n := by rw [htlen]; omega
        have hrec : IsChunking (encoded.drop c) body :=
          ih (encoded.drop c).length hlt (encoded.drop c) body c' rfl hinner hc'full
        rw [hbuf]
        exact IsChunking.chunk digits data (encoded.drop c) body hdig hsz hle hne hrec

/-! ## The refinement theorem -/

/-- **Refinement (correctness).** The decoder accepts `encoded` and returns
`plain` **iff** `encoded` is a valid chunked encoding of `plain`. So `dechunk`
recovers exactly the concatenated chunk payloads — no chunk dropped, no
chunk-size mis-counted, no framing octet leaked. -/
theorem dechunk_iff_spec (encoded plain : Bytes) :
    dechunk encoded = some plain ↔ IsChunking encoded plain := by
  constructor
  · intro h
    unfold dechunk at h
    split at h
    · rename_i body consumed heq
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        exact decodeStream_sound encoded.length encoded body consumed rfl heq hc
      · simp at h
    · simp at h
  · intro h
    have hds := isChunking_decodeStream encoded plain h
    unfold dechunk
    rw [hds]
    simp

/-! ## Non-vacuity -/

/-- The canonical `encodeStream` image lands in `IsChunking` — a bridge from the
`Body/Chunked.lean` round-trip world to the declarative spec. -/
theorem isChunking_encodeStream (chunks : List Bytes)
    (hne : ∀ d ∈ chunks, d ≠ []) (hle : ∀ d ∈ chunks, d.length ≤ maxChunkSize) :
    IsChunking (encodeStream chunks) chunks.flatten := by
  induction chunks with
  | nil =>
    show IsChunking encodeTerminal []
    have e : encodeTerminal = toHex 0 ++ CR :: LF :: CR :: LF :: [] := by
      simp [encodeTerminal, List.append_assoc]
    rw [e]
    exact IsChunking.terminal (toHex 0) (toHex_no_cr 0) (parseHex_toHex 0)
  | cons d ds ih =>
    have hne_d : d ≠ [] := hne d (by simp)
    have hle_d : d.length ≤ maxChunkSize := hle d (by simp)
    have hne_ds : ∀ x ∈ ds, x ≠ [] := fun x hx => hne x (by simp [hx])
    have hle_ds : ∀ x ∈ ds, x.length ≤ maxChunkSize := fun x hx => hle x (by simp [hx])
    have e : encodeStream (d :: ds)
        = toHex d.length ++ CR :: LF :: d ++ CR :: LF :: encodeStream ds := by
      simp [encodeStream, encodeChunk, List.append_assoc]
    rw [e, List.flatten_cons]
    exact IsChunking.chunk (toHex d.length) d (encodeStream ds) ds.flatten
      (toHex_no_cr d.length) (by rw [parseHex_toHex]) hle_d hne_d (ih hne_ds hle_ds)

/-- A concrete multi-chunk vector: two data chunks `AB` (0x41 0x42) and `CDE`
(0x43 0x44 0x45), then the terminal. The decoder delivers exactly the
concatenation `ABCDE`. A decoder that dropped either chunk, or mis-counted a
size, would deliver different bytes and fail this equation. -/
theorem dechunk_two_chunk_vector :
    dechunk (encodeStream [[0x41, 0x42], [0x43, 0x44, 0x45]])
      = some [0x41, 0x42, 0x43, 0x44, 0x45] := by
  have hspec : IsChunking (encodeStream [[0x41, 0x42], [0x43, 0x44, 0x45]])
      ([[0x41, 0x42], [0x43, 0x44, 0x45]] : List Bytes).flatten := by
    apply isChunking_encodeStream
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> simp
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> simp [maxChunkSize]
  have he : ([[0x41, 0x42], [0x43, 0x44, 0x45]] : List Bytes).flatten
      = [0x41, 0x42, 0x43, 0x44, 0x45] := by simp
  rw [← he]
  exact (dechunk_iff_spec _ _).mpr hspec

/-- Non-vacuity, the other way: the exact-payload requirement is real. `ABCDE` is
the *only* payload the two-chunk vector decodes to, so the shorter `AB` (what a
decoder that dropped the second chunk would yield) is rejected. -/
theorem dechunk_two_chunk_rejects_dropped :
    dechunk (encodeStream [[0x41, 0x42], [0x43, 0x44, 0x45]]) ≠ some [0x41, 0x42] := by
  rw [dechunk_two_chunk_vector]; simp

end Chunked
end Body
