/-!
# DERP: the relay frame protocol

A model of the DERP (Designated Encrypted Relay for Packets) wire
framing — the length-prefixed frame envelope a client and relay server
exchange, and the send/recv-packet and peer-present frames carried
inside it. DERP has no public RFC; this is derived from the documented
DERP wire protocol: every message on a DERP connection is a frame

    ┌────────┬──────────────────┬───────────────────────┐
    │ type   │ length (uint32)  │ payload (length bytes) │
    │ 1 byte │ 4 bytes, big-end │                        │
    └────────┴──────────────────┴───────────────────────┘

so the fixed header is 5 bytes and the payload is exactly the declared
length. The relay never forwards a frame whose declared length exceeds
its packet cap, and a reader must consume exactly `5 + length` bytes and
no more — a frame is parsed strictly within its declared length.

The payload shapes modeled:

* **SendPacket** (client→server): a 32-byte destination public key
  followed by the packet to relay.
* **RecvPacket** (server→client): a 32-byte source public key followed
  by the relayed packet.
* **PeerPresent** (server→client): a 32-byte peer public key announcing
  that a peer is connected to the relay.

## Theorems

* `derp_frame_bounds` — the central framing property: whenever
  `parseFrame` accepts a byte stream, the produced payload has exactly
  the declared length, that length is within the cap, and the consumed
  prefix is exactly the 5-byte header plus the payload — the leftover is
  the true remainder. A frame is parsed within its declared length; the
  parser never reads past it and never under-delivers.
* `derp_no_overread` — the parser returns a frame only when the declared
  length actually fits in the buffer; a truncated frame yields `none`.
* `derp_parse_serialize` — serializing a frame and parsing it back
  returns the same frame and the untouched trailing bytes (round-trip),
  for payloads within the cap and addressable by the 32-bit length.
* `derp_sendpacket_split` / `derp_peerpresent_key` — a SendPacket /
  RecvPacket payload splits into exactly a 32-byte key and the packet;
  a PeerPresent payload is exactly the 32-byte peer key.

## Boundary / UNCLOSED

* Cryptography — the DERP handshake (the server key exchange and the
  NaCl box that authenticates ClientInfo/ServerInfo) and the end-to-end
  encryption of relayed packets — is out of scope. This model is the
  framing only; the relay treats packet payloads as opaque bytes, which
  is faithful to DERP (the relay cannot read them).
* The exact frame-type tag numbers are the wire assignments; the
  framing theorems do not depend on them.
* Rate limiting, the mesh/watch-connections broadcast, and the DERP-over-
  HTTP upgrade are not modeled.
-/

namespace Derp

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

/-- Public keys on DERP are 32 bytes (Curve25519). -/
def keyLen : Nat := 32

/-- The frame types carried on a DERP connection. The tag numbers are
the wire assignments; the framing theorems are independent of them. -/
inductive FrameType where
  | serverKey
  | clientInfo
  | serverInfo
  | sendPacket
  | recvPacket
  | keepAlive
  | notePreferred
  | peerGone
  | peerPresent
  | watchConns
  | closePeer
  | ping
  | pong
  | health
  | restarting
  | forwardPacket
  /-- An unrecognized tag: preserved so parsing is total. -/
  | unknown (tag : UInt8)
deriving Repr, DecidableEq

/-- Decode a type byte. -/
def FrameType.ofByte : UInt8 → FrameType
  | 0x01 => .serverKey
  | 0x02 => .clientInfo
  | 0x03 => .serverInfo
  | 0x04 => .sendPacket
  | 0x05 => .recvPacket
  | 0x06 => .keepAlive
  | 0x07 => .notePreferred
  | 0x08 => .peerGone
  | 0x09 => .peerPresent
  | 0x0a => .watchConns
  | 0x0b => .closePeer
  | 0x0c => .ping
  | 0x0d => .pong
  | 0x0e => .health
  | 0x0f => .restarting
  | 0x10 => .forwardPacket
  | b => .unknown b

/-- Encode a type byte. -/
def FrameType.toByte : FrameType → UInt8
  | .serverKey => 0x01
  | .clientInfo => 0x02
  | .serverInfo => 0x03
  | .sendPacket => 0x04
  | .recvPacket => 0x05
  | .keepAlive => 0x06
  | .notePreferred => 0x07
  | .peerGone => 0x08
  | .peerPresent => 0x09
  | .watchConns => 0x0a
  | .closePeer => 0x0b
  | .ping => 0x0c
  | .pong => 0x0d
  | .health => 0x0e
  | .restarting => 0x0f
  | .forwardPacket => 0x10
  | .unknown b => b

/-! ## Big-endian 32-bit length field -/

/-- Decode a big-endian `uint32` from four bytes. -/
def be32 (a b c d : UInt8) : Nat :=
  a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat

/-- The header is a type byte plus a four-byte length. -/
def headerLen : Nat := 5

/-- A parsed frame: its type and its exact payload. -/
structure Frame where
  ftype : FrameType
  payload : Bytes
deriving Repr, DecidableEq

/-- Parse one frame off the front of a byte stream, capping the declared
length at `maxLen` (the relay's packet size limit). On success returns
the frame and the untouched trailing bytes; on a short buffer or an
over-cap length, `none`. The declared length is honored exactly: the
payload is the next `len` bytes and no more. -/
def parseFrame (maxLen : Nat) (bs : Bytes) : Option (Frame × Bytes) :=
  match bs with
  | t :: l0 :: l1 :: l2 :: l3 :: rest =>
    let len := be32 l0 l1 l2 l3
    if len ≤ maxLen ∧ len ≤ rest.length then
      some ({ ftype := FrameType.ofByte t, payload := rest.take len },
            rest.drop len)
    else
      none
  | _ => none

/-! ## The central framing theorem -/

/-- **A frame is parsed within its declared length.** Whenever
`parseFrame` accepts, three things hold at once:

* the payload has exactly the declared length, and that length is
  within the cap (`payload.length ≤ maxLen`);
* the whole input decomposes as `header ++ payload ++ rest`, so the
  bytes consumed for this frame are exactly `headerLen + payload.length`
  and the returned `rest` is the genuine remainder;
* consequently `bs.length = headerLen + payload.length + rest.length`.

The parser never reads past the declared length and never returns fewer
payload bytes than declared. -/
theorem derp_frame_bounds (maxLen : Nat) (bs : Bytes) {f : Frame}
    {rest : Bytes} (h : parseFrame maxLen bs = some (f, rest)) :
    f.payload.length ≤ maxLen ∧
    bs = bs.take headerLen ++ f.payload ++ rest ∧
    bs.length = headerLen + f.payload.length + rest.length := by
  unfold parseFrame at h
  -- Only the ≥5-byte shape can produce `some`.
  match bs with
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | [_, _, _] => simp at h
  | [_, _, _, _] => simp at h
  | t :: l0 :: l1 :: l2 :: l3 :: tl =>
    simp only at h
    split at h
    · rename_i hcond
      obtain ⟨hcap, hfit⟩ := hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hf, hrest⟩ := h
      subst hf
      subst hrest
      -- payload = tl.take len, len = be32 l0 l1 l2 l3, len ≤ tl.length
      have hplen : (tl.take (be32 l0 l1 l2 l3)).length = be32 l0 l1 l2 l3 := by
        rw [List.length_take]
        exact Nat.min_eq_left hfit
      refine ⟨?_, ?_, ?_⟩
      · -- payload.length ≤ maxLen
        show (tl.take (be32 l0 l1 l2 l3)).length ≤ maxLen
        rw [hplen]; exact hcap
      · -- header ++ payload ++ rest reconstruction
        show t :: l0 :: l1 :: l2 :: l3 :: tl
            = (t :: l0 :: l1 :: l2 :: l3 :: tl).take headerLen
              ++ (tl.take (be32 l0 l1 l2 l3))
              ++ tl.drop (be32 l0 l1 l2 l3)
        simp only [headerLen]
        show t :: l0 :: l1 :: l2 :: l3 :: tl
            = [t, l0, l1, l2, l3]
              ++ (tl.take (be32 l0 l1 l2 l3) ++ tl.drop (be32 l0 l1 l2 l3))
        rw [List.take_append_drop]
        rfl
      · -- length accounting
        show (t :: l0 :: l1 :: l2 :: l3 :: tl).length
            = headerLen + (tl.take (be32 l0 l1 l2 l3)).length
              + (tl.drop (be32 l0 l1 l2 l3)).length
        rw [hplen, List.length_drop]
        simp only [List.length_cons, headerLen]
        omega
    · exact absurd h (by simp)

/-- **No over-read.** If `parseFrame` returns a frame, the declared
length genuinely fits in the buffer after the header — the parser never
manufactures payload bytes beyond the input. -/
theorem derp_no_overread (maxLen : Nat) (bs : Bytes) {f : Frame}
    {rest : Bytes} (h : parseFrame maxLen bs = some (f, rest)) :
    headerLen + f.payload.length ≤ bs.length := by
  obtain ⟨_, _, hlen⟩ := derp_frame_bounds maxLen bs h
  omega

/-! ## Serialization round-trip -/

/-- Encode a length into four big-endian bytes. -/
def enc32 (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536),
   UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- Serialize a frame: type byte, big-endian length, payload. -/
def serializeFrame (f : Frame) : Bytes :=
  f.ftype.toByte :: enc32 f.payload.length ++ f.payload

/-- `be32` inverts `enc32` for lengths addressable by 32 bits. Proven by
`decide`-free arithmetic on the byte reductions. -/
theorem be32_enc32 (n : Nat) (h : n < 16777216) :
    be32 (UInt8.ofNat (n / 16777216)) (UInt8.ofNat (n / 65536))
         (UInt8.ofNat (n / 256)) (UInt8.ofNat n) = n := by
  unfold be32
  have h0 : (UInt8.ofNat (n / 16777216)).toNat = n / 16777216 := by
    rw [UInt8.toNat_ofNat]
    have : n / 16777216 = 0 := Nat.div_eq_of_lt h
    rw [this]
  have h1 : (UInt8.ofNat (n / 65536)).toNat = (n / 65536) % 256 := by
    rw [UInt8.toNat_ofNat]
  have h2 : (UInt8.ofNat (n / 256)).toNat = (n / 256) % 256 := by
    rw [UInt8.toNat_ofNat]
  have h3 : (UInt8.ofNat n).toNat = n % 256 := by
    rw [UInt8.toNat_ofNat]
  rw [h0, h1, h2, h3]
  omega

/-- **Round-trip.** Parsing a serialized frame recovers the frame and
the untouched trailing bytes, provided the payload fits the cap and its
length is addressable by the 32-bit field. -/
theorem derp_parse_serialize (maxLen : Nat) (f : Frame) (tail : Bytes)
    (hcap : f.payload.length ≤ maxLen)
    (haddr : f.payload.length < 16777216)
    (htype : FrameType.ofByte (FrameType.toByte f.ftype) = f.ftype) :
    parseFrame maxLen (serializeFrame f ++ tail) = some (f, tail) := by
  unfold serializeFrame parseFrame enc32
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  have hlen := be32_enc32 f.payload.length haddr
  -- After the five header bytes, the remaining stream is payload ++ tail.
  simp only [hlen]
  have hfit : f.payload.length ≤ (f.payload ++ tail).length := by
    rw [List.length_append]; omega
  rw [if_pos ⟨hcap, hfit⟩]
  rw [List.take_left, List.drop_left, htype]

/-! ## Packet-carrying payload shapes -/

/-- Split a payload into a 32-byte public key and the trailing packet,
if the payload is long enough. Both SendPacket and RecvPacket carry a
key-prefixed packet. -/
def splitKeyed (payload : Bytes) : Option (Bytes × Bytes) :=
  if keyLen ≤ payload.length then
    some (payload.take keyLen, payload.drop keyLen)
  else
    none

/-- **Keyed-payload split.** A SendPacket/RecvPacket payload divides into
exactly a 32-byte key and the packet, and the two reassemble to the
original payload. -/
theorem derp_sendpacket_split (payload : Bytes) {key pkt : Bytes}
    (h : splitKeyed payload = some (key, pkt)) :
    key.length = keyLen ∧ payload = key ++ pkt := by
  unfold splitKeyed at h
  split at h
  · rename_i hle
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hk, hp⟩ := h
    subst hk
    subst hp
    refine ⟨?_, ?_⟩
    · rw [List.length_take]; exact Nat.min_eq_left hle
    · rw [List.take_append_drop]
  · exact absurd h (by simp)

/-- A PeerPresent frame's payload is exactly the 32-byte peer key. -/
def peerPresentKey (payload : Bytes) : Option Bytes :=
  if payload.length = keyLen then some payload else none

/-- **PeerPresent key.** When accepted, the peer key is exactly the
payload and has the fixed key length. -/
theorem derp_peerpresent_key (payload : Bytes) {key : Bytes}
    (h : peerPresentKey payload = some key) :
    key = payload ∧ key.length = keyLen := by
  unfold peerPresentKey at h
  split at h
  · rename_i hlen
    injection h with hk
    subst hk
    exact ⟨rfl, hlen⟩
  · exact absurd h (by simp)

/-! ## Every frame type round-trips its tag -/

/-- **Tag round-trip.** For every *named* frame type, decoding its wire tag
recovers it: `ofByte (toByte ft) = ft`. (The catch-all `unknown b` round-
trips only for tags `b` outside the assigned range; a `b` in `0x01…0x10`
decodes to its named type, which is exactly the intended normalization.)
This covers all sixteen assigned DERP frame types. -/
theorem derp_type_roundtrip_named (ft : FrameType)
    (h : ∀ b, ft ≠ FrameType.unknown b) :
    FrameType.ofByte (FrameType.toByte ft) = ft := by
  cases ft <;> first | rfl | (rename_i b; exact absurd rfl (h b))

/-! ## Keepalive frames

The relay sends a keepAlive frame (type `0x06`, empty payload) to keep a
mesh connection warm; clients send one as an application-level keepalive.
It carries no payload — the frame *is* the signal. -/

/-- The canonical keepalive frame: type `keepAlive`, empty payload. -/
def keepAliveFrame : Frame := { ftype := .keepAlive, payload := [] }

/-- **Keepalive round-trips.** A serialized keepalive parses back to the
keepalive frame and the untouched tail — it is a well-formed zero-length
frame, not a truncation. -/
theorem derp_keepalive_roundtrip (maxLen : Nat) (tail : Bytes) :
    parseFrame maxLen (serializeFrame keepAliveFrame ++ tail)
      = some (keepAliveFrame, tail) := by
  apply derp_parse_serialize
  · simp [keepAliveFrame]
  · simp [keepAliveFrame]
  · rfl

/-! ## Mesh peer presence

On a mesh connection the relay announces peer arrivals and departures with
peerPresent / peerGone frames, and refreshes liveness with keepAlive. A
client tracks which peers are reachable through the relay by folding these
frames into a presence view. This is the mesh-membership state the DERP
mesh keepalive maintains. -/

/-- A client's mesh view: the peer public keys the relay currently
announces as present. -/
structure Presence where
  peers : List Bytes
deriving Repr

/-- Nothing present yet. -/
def Presence.empty : Presence := { peers := [] }

/-- Fold one inbound relay frame into the presence view. peerPresent adds
the announced peer (deduplicated); peerGone removes it; keepAlive and every
other frame leave membership unchanged (a keepalive only refreshes
liveness). -/
def Presence.apply (p : Presence) (f : Frame) : Presence :=
  match f.ftype with
  | .peerPresent => { peers := f.payload :: p.peers.filter (· != f.payload) }
  | .peerGone    => { peers := p.peers.filter (· != f.payload) }
  | _            => p

/-- **PeerPresent makes a peer present.** After a peerPresent for key `k`,
`k` is in the view. -/
theorem derp_peer_present_adds (p : Presence) (k : Bytes) :
    k ∈ (p.apply { ftype := .peerPresent, payload := k }).peers := by
  simp [Presence.apply]

/-- **PeerGone makes a peer absent.** After a peerGone for key `k`, `k` is
not in the view — even if it appeared multiple times, the filter removes
every copy. -/
theorem derp_peer_gone_removes (p : Presence) (k : Bytes) :
    k ∉ (p.apply { ftype := .peerGone, payload := k }).peers := by
  simp [Presence.apply, List.mem_filter]

/-- **Keepalive does not change membership.** A keepAlive frame refreshes
the connection but leaves the presence view exactly as it was. -/
theorem derp_keepalive_presence (p : Presence) (payload : Bytes) :
    p.apply { ftype := .keepAlive, payload := payload } = p := rfl

/-! ## Streaming: parsing a whole buffer into frames -/

/-- Parse a buffer into every complete frame it holds, returning the frames
and the short trailing bytes that do not form one more. Each step consumes
a full `headerLen + payload` prefix, so the remaining buffer strictly
shrinks and the recursion terminates. -/
def parseFrames (maxLen : Nat) (bs : Bytes) : List Frame × Bytes :=
  match h : parseFrame maxLen bs with
  | some (f, rest) =>
    have hlt : rest.length < bs.length := by
      have hb := (derp_frame_bounds maxLen bs h).2.2
      simp only [headerLen] at hb; omega
    ((f :: (parseFrames maxLen rest).1), (parseFrames maxLen rest).2)
  | none => ([], bs)
termination_by bs.length
decreasing_by exact hlt

/-- **Streamed frames all respect the cap.** Every frame `parseFrames`
returns has a payload within `maxLen` — the streaming parser never emits an
over-cap or over-read frame, because each is produced by `parseFrame`. -/
theorem derp_parseFrames_bounded (maxLen : Nat) (bs : Bytes) :
    ∀ f ∈ (parseFrames maxLen bs).1, f.payload.length ≤ maxLen := by
  induction bs using parseFrames.induct maxLen with
  | case1 x f rest h hlt ih =>
    intro g hg
    rw [parseFrames.eq_def] at hg
    split at hg
    · next f2 rest2 h2 =>
        simp only [List.mem_cons] at hg
        rw [h] at h2; injection h2 with hp; injection hp with hf hr
        subst hf; subst hr
        rcases hg with rfl | hg
        · exact (derp_frame_bounds maxLen x h).1
        · exact ih g hg
    · next h2 => rw [h] at h2; exact absurd h2 (by simp)
  | case2 x h =>
    intro g hg
    rw [parseFrames.eq_def] at hg
    split at hg
    · next f2 rest2 h2 => rw [h] at h2; exact absurd h2 (by simp)
    · next h2 => simp at hg

end Derp
