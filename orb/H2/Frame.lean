import H2.Basic

/-!
# HTTP/2 frames (RFC 9113 §4, §6)

Every HTTP/2 frame begins with a fixed **9-octet header**:

```text
+-----------------------------------------------+
|                 Length (24)                   |
+---------------+---------------+---------------+
|   Type (8)    |   Flags (8)   |
+-+-------------+---------------+-------------------------------+
|R|                 Stream Identifier (31)                     |
+=+=============================================================+
|                   Frame Payload (0...)                     ...
+---------------------------------------------------------------+
```

* `parseHeader` — the total 9-octet header parser. The `R` bit (bit 31 of the
  stream-identifier word) is **reserved and masked to zero on parse**
  (RFC 9113 §4.1) — `parseHeader_reserved_clear`. Length is a 24-bit field
  (`parseHeader_length_lt`) and the stream id a 31-bit field
  (`parseHeader_streamId_lt`).
* `FrameType.ofNat` — the frame taxonomy (RFC 9113 §6), total on all `2^8`
  type octets: everything outside the known set maps to `unknown`
  (`FrameType.ofNat_unknown`). Unknown types are decoded and skipped, not
  rejected (RFC 9113 §4.1) — `decode_unknown_skip`.
* `decode` — the frame decoder into `complete / incomplete / tooLarge / error`.
  **Totality** is `FrameType.ofNat`'s totality plus the header/completeness
  guards; **consumed-monotonicity** is `decode_consumed`
  (`9 ≤ consumed ≤ input length` — every frame advances by at least the header
  and never over-reads); the **frame-size-limit** check is `decode_tooLarge`
  (a declared length above `maxFrameSize` is rejected before any payload is
  read) with its converse `decode_complete_size` (a completed frame's declared
  length is always within the limit).

Deliberately at the header level only: per-type payload validation
(padding, PRIORITY stripping, the RST_STREAM/WINDOW_UPDATE/PING fixed-length
rules, stream-id-must-be-zero rules) is a scope cut, deferred to the framing
-semantics rung (see the notes).
-/

namespace H2

/-- The fixed HTTP/2 frame-header size, in octets (RFC 9113 §4.1). -/
def frameHeaderSize : Nat := 9

theorem u8_toNat_lt (x : UInt8) : x.toNat < 256 := x.toBitVec.isLt

/-! ## The 9-octet frame header -/

/-- A parsed HTTP/2 frame header. All fields are the decoded integer values;
`streamId` already has the reserved bit cleared. -/
structure FrameHeader where
  /-- Payload length (24-bit field). -/
  length : Nat
  /-- Frame type (8-bit field). -/
  frameType : Nat
  /-- Frame flags (8-bit field). -/
  flags : Nat
  /-- Stream identifier (31-bit field; reserved bit masked to zero). -/
  streamId : Nat
deriving Repr, DecidableEq

/-- Parse the 9 header octets into a `FrameHeader`. The stream-identifier word
is masked by `% 2 ^ 31`, which is exactly clearing the reserved high bit
(`R`, bit 31) of the big-endian 32-bit word (RFC 9113 §4.1). -/
def parseHeaderAux (b0 b1 b2 b3 b4 b5 b6 b7 b8 : UInt8) : FrameHeader :=
  { length := b0.toNat * 2 ^ 16 + b1.toNat * 2 ^ 8 + b2.toNat
    frameType := b3.toNat
    flags := b4.toNat
    streamId :=
      (b5.toNat * 2 ^ 24 + b6.toNat * 2 ^ 16 + b7.toNat * 2 ^ 8 + b8.toNat) % 2 ^ 31 }

/-- Parse a frame header from the head of `bs`. `none` iff fewer than 9 octets
are present (the caller waits for more transport bytes). -/
def parseHeader : Bytes → Option FrameHeader
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: _ =>
    some (parseHeaderAux b0 b1 b2 b3 b4 b5 b6 b7 b8)
  | _ => none

/-- **Header-parse totality**: 9 or more octets always parse to a header. -/
theorem parseHeader_isSome (bs : Bytes) (h : frameHeaderSize ≤ bs.length) :
    (parseHeader bs).isSome := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ |
    ⟨b6, _ | ⟨b7, _ | ⟨b8, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first
      | (simp only [parseHeader]; rfl)
      | (simp only [frameHeaderSize, List.length_cons, List.length_nil] at h; omega)

/-- **Reserved-bit mask**: the parsed stream identifier always has the reserved
high bit clear — it is a 31-bit value (RFC 9113 §4.1). -/
theorem parseHeader_reserved_clear (b0 b1 b2 b3 b4 b5 b6 b7 b8 : UInt8) :
    (parseHeaderAux b0 b1 b2 b3 b4 b5 b6 b7 b8).streamId < 2 ^ 31 := by
  show (_ % 2 ^ 31) < 2 ^ 31
  exact Nat.mod_lt _ (by decide)

/-- The parsed length is a 24-bit value. -/
theorem parseHeader_length_lt (b0 b1 b2 b3 b4 b5 b6 b7 b8 : UInt8) :
    (parseHeaderAux b0 b1 b2 b3 b4 b5 b6 b7 b8).length < 2 ^ 24 := by
  show b0.toNat * 2 ^ 16 + b1.toNat * 2 ^ 8 + b2.toNat < 2 ^ 24
  have h0 := u8_toNat_lt b0
  have h1 := u8_toNat_lt b1
  have h2 := u8_toNat_lt b2
  omega

/-! ## The frame taxonomy (RFC 9113 §6) -/

/-- The HTTP/2 frame taxonomy (RFC 9113 §6). `unknown` carries the raw type
octet. -/
inductive FrameType where
  | data
  | headers
  | priority
  | rstStream
  | settings
  | pushPromise
  | ping
  | goaway
  | windowUpdate
  | continuation
  | unknown (t : Nat)
deriving Repr, DecidableEq

/-- Total classification of a type octet (RFC 9113 §6.1–§6.10). -/
def FrameType.ofNat (t : Nat) : FrameType :=
  if t = 0x0 then .data
  else if t = 0x1 then .headers
  else if t = 0x2 then .priority
  else if t = 0x3 then .rstStream
  else if t = 0x4 then .settings
  else if t = 0x5 then .pushPromise
  else if t = 0x6 then .ping
  else if t = 0x7 then .goaway
  else if t = 0x8 then .windowUpdate
  else if t = 0x9 then .continuation
  else .unknown t

/-- The known (structured) frame-type octets. -/
def isKnownType (t : Nat) : Bool :=
  t = 0x0 || t = 0x1 || t = 0x2 || t = 0x3 || t = 0x4 || t = 0x5 || t = 0x6 ||
    t = 0x7 || t = 0x8 || t = 0x9

/-- **Taxonomy totality**: every type octet outside the known set classifies
as `unknown` — the taxonomy is total. -/
theorem FrameType.ofNat_unknown (t : Nat) (h : isKnownType t = false) :
    FrameType.ofNat t = .unknown t := by
  unfold isKnownType at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  unfold FrameType.ofNat
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-! ## Frames and the decoder -/

/-- `true` iff bit `bit` of `flags` is set. -/
def flagSet (flags bit : Nat) : Bool := decide (flags / 2 ^ bit % 2 = 1)

/-- A decoded HTTP/2 frame. Payloads are carried raw (unpadded, priority not
stripped — those are the deferred framing-semantics layer); flags that the
per-stream FSM consumes (`END_STREAM`, `END_HEADERS`, `ACK`) are surfaced. -/
inductive Frame where
  /-- DATA (0x0). -/
  | data (streamId : Nat) (endStream : Bool) (payload : Bytes)
  /-- HEADERS (0x1): an HPACK-encoded header block (see `H2.Hpack`). -/
  | headers (streamId : Nat) (endStream endHeaders : Bool) (payload : Bytes)
  /-- PRIORITY (0x2). -/
  | priority (streamId : Nat) (payload : Bytes)
  /-- RST_STREAM (0x3). -/
  | rstStream (streamId : Nat) (payload : Bytes)
  /-- SETTINGS (0x4). -/
  | settings (streamId : Nat) (ack : Bool) (payload : Bytes)
  /-- PUSH_PROMISE (0x5). -/
  | pushPromise (streamId : Nat) (payload : Bytes)
  /-- PING (0x6). -/
  | ping (streamId : Nat) (ack : Bool) (payload : Bytes)
  /-- GOAWAY (0x7). -/
  | goaway (streamId : Nat) (payload : Bytes)
  /-- WINDOW_UPDATE (0x8). -/
  | windowUpdate (streamId : Nat) (payload : Bytes)
  /-- CONTINUATION (0x9): a header-block continuation. -/
  | continuation (streamId : Nat) (endHeaders : Bool) (payload : Bytes)
  /-- Unknown/extension type: skipped per RFC 9113 §4.1 (payload discarded). -/
  | unknown (frameType streamId len : Nat)
deriving Repr, DecidableEq

/-- Outcome of one frame decode step. `tooLarge` carries the offending declared
length; `error` is reserved for the deferred per-type validation layer. -/
inductive FrameResult where
  | complete (frame : Frame) (consumed : Nat)
  | incomplete
  | tooLarge (len : Nat)
  | error
deriving Repr, DecidableEq

/-- Decode one frame from the head of `bs`, given the peer's advertised
`maxFrameSize` (SETTINGS_MAX_FRAME_SIZE).

Header parse → **frame-size-limit check** → payload-completeness check →
taxonomy dispatch. A frame consumes `9 + length` octets exactly. Unknown types
are skipped (`.unknown` retaining type/stream/length, payload discarded). -/
def decode (bs : Bytes) (maxFrameSize : Nat) : FrameResult :=
  match parseHeader bs with
  | none => .incomplete
  | some hdr =>
    if maxFrameSize < hdr.length then .tooLarge hdr.length
    else if bs.length < 9 + hdr.length then .incomplete
    else
      let payload := (bs.drop 9).take hdr.length
      match FrameType.ofNat hdr.frameType with
      | .data =>
        .complete (.data hdr.streamId (flagSet hdr.flags 0) payload) (9 + hdr.length)
      | .headers =>
        .complete (.headers hdr.streamId (flagSet hdr.flags 0) (flagSet hdr.flags 2) payload)
          (9 + hdr.length)
      | .priority => .complete (.priority hdr.streamId payload) (9 + hdr.length)
      | .rstStream => .complete (.rstStream hdr.streamId payload) (9 + hdr.length)
      | .settings =>
        .complete (.settings hdr.streamId (flagSet hdr.flags 0) payload) (9 + hdr.length)
      | .pushPromise => .complete (.pushPromise hdr.streamId payload) (9 + hdr.length)
      | .ping =>
        .complete (.ping hdr.streamId (flagSet hdr.flags 0) payload) (9 + hdr.length)
      | .goaway => .complete (.goaway hdr.streamId payload) (9 + hdr.length)
      | .windowUpdate => .complete (.windowUpdate hdr.streamId payload) (9 + hdr.length)
      | .continuation =>
        .complete (.continuation hdr.streamId (flagSet hdr.flags 2) payload) (9 + hdr.length)
      | .unknown t => .complete (.unknown t hdr.streamId hdr.length) (9 + hdr.length)

/-! ## Structural inversion of a completed decode -/

/-- **Completed-decode inversion**: whenever `decode` completes, the header
parsed, its declared length was within `maxFrameSize` (the frame-size-limit
check passed), the frame consumed exactly `9 + length` octets, and that many
octets were present. Consumed-monotonicity and the size-limit corollary both
follow from this. -/
theorem decode_complete_inv (bs : Bytes) (mfs : Nat) (f : Frame) (n : Nat)
    (h : decode bs mfs = .complete f n) :
    ∃ hdr, parseHeader bs = some hdr ∧ hdr.length ≤ mfs ∧
      n = 9 + hdr.length ∧ 9 + hdr.length ≤ bs.length := by
  unfold decode at h
  split at h
  · exact absurd h (by simp)
  · rename_i hdr hp
    split at h
    · exact absurd h (by simp)
    · rename_i hsz
      split at h
      · exact absurd h (by simp)
      · rename_i hcomp
        simp only [] at h
        repeat' split at h
        all_goals (cases h; exact ⟨hdr, hp, by omega, rfl, by omega⟩)

/-- **Consumed-monotonicity**: a completed frame consumes at least the 9-octet
header (progress — a frame loop strictly advances) and never more than the
input holds (boundedness — no over-read). -/
theorem decode_consumed (bs : Bytes) (mfs : Nat) (f : Frame) (n : Nat)
    (h : decode bs mfs = .complete f n) : frameHeaderSize ≤ n ∧ n ≤ bs.length := by
  obtain ⟨hdr, _, _, hn, hle⟩ := decode_complete_inv bs mfs f n h
  unfold frameHeaderSize
  omega

theorem decode_consumed_pos (bs : Bytes) (mfs : Nat) (f : Frame) (n : Nat)
    (h : decode bs mfs = .complete f n) : 1 ≤ n := by
  have := (decode_consumed bs mfs f n h).1
  unfold frameHeaderSize at this
  omega

theorem decode_consumed_le (bs : Bytes) (mfs : Nat) (f : Frame) (n : Nat)
    (h : decode bs mfs = .complete f n) : n ≤ bs.length :=
  (decode_consumed bs mfs f n h).2

/-- **Frame-size-limit — completed direction**: any frame that completes had a
declared length within `maxFrameSize`. -/
theorem decode_complete_size (bs : Bytes) (mfs : Nat) (f : Frame) (n : Nat)
    (h : decode bs mfs = .complete f n) :
    ∃ hdr, parseHeader bs = some hdr ∧ hdr.length ≤ mfs := by
  obtain ⟨hdr, hp, hlen, _⟩ := decode_complete_inv bs mfs f n h
  exact ⟨hdr, hp, hlen⟩

/-- **Frame-size-limit — rejection direction**: a header whose declared length
exceeds `maxFrameSize` is rejected as `tooLarge` before any payload is read
(RFC 9113 §4.2). -/
theorem decode_tooLarge (bs : Bytes) (mfs : Nat) (hdr : FrameHeader)
    (hp : parseHeader bs = some hdr) (hsz : mfs < hdr.length) :
    decode bs mfs = .tooLarge hdr.length := by
  unfold decode
  rw [hp]
  simp only []
  rw [if_pos hsz]

/-- **Unknown-type skip** (RFC 9113 §4.1): a frame of any unknown type with a
within-limit, fully present payload decodes to `.unknown` (type/stream/length
retained, payload discarded) and consumes header + payload — unknown types are
never rejected. -/
theorem decode_unknown_skip (bs : Bytes) (mfs : Nat) (hdr : FrameHeader)
    (hp : parseHeader bs = some hdr) (hunk : isKnownType hdr.frameType = false)
    (hsz : hdr.length ≤ mfs) (hcomp : 9 + hdr.length ≤ bs.length) :
    decode bs mfs = .complete (.unknown hdr.frameType hdr.streamId hdr.length) (9 + hdr.length) := by
  unfold decode
  rw [hp]
  simp only []
  rw [if_neg (by omega), if_neg (by omega), FrameType.ofNat_unknown hdr.frameType hunk]

/-! ## Wire vectors, checker-verified -/

/-- DATA on stream 1, `END_STREAM` set, 3-byte payload: 9-octet header
`00 00 03 | 00 | 01 | 00 00 00 01` then `aa bb cc`. -/
example : decode [0x00, 0x00, 0x03, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
    0xaa, 0xbb, 0xcc] 16384
    = .complete (.data 1 true [0xaa, 0xbb, 0xcc]) 12 := rfl

/-- HEADERS on stream 3, `END_HEADERS` (0x04) set, `END_STREAM` clear. -/
example : decode [0x00, 0x00, 0x02, 0x01, 0x04, 0x00, 0x00, 0x00, 0x03,
    0x82, 0x86] 16384
    = .complete (.headers 3 false true [0x82, 0x86]) 11 := rfl

/-- The reserved high bit of the stream-id word is cleared: the same header
with `stream_id = 0x8000_0001` parses to stream 1. -/
example : decode [0x00, 0x00, 0x00, 0x08, 0x00, 0x80, 0x00, 0x00, 0x01] 16384
    = .complete (.windowUpdate 1 []) 9 := rfl

/-- Unknown type `0x0b` with a 2-byte payload: skipped, not rejected. -/
example : decode [0x00, 0x00, 0x02, 0x0b, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xde, 0xad] 16384
    = .complete (.unknown 0x0b 0 2) 11 := rfl

/-- A declared length above `maxFrameSize` is rejected. -/
example : decode [0x00, 0x40, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01] 16384
    = .tooLarge 16385 := rfl

/-- Fewer than 9 octets: incomplete, not an error. -/
example : decode [0x00, 0x00, 0x03, 0x00] 16384 = .incomplete := rfl

/-- Header present but payload truncated: incomplete. -/
example : decode [0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01] 16384
    = .incomplete := rfl

end H2
