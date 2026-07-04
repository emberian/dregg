/-!
# WebRTC data channels: DCEP handshake and stream parity (RFC 8832 / RFC 8831)

A total model of the Data Channel Establishment Protocol (DCEP, RFC 8832) that
opens a WebRTC data channel over an SCTP association, together with the SCTP
stream-identifier parity rule (RFC 8831 §6.5, RFC 8832 §6) that keeps the two
peers from colliding on stream numbers.

## What this file captures

* **RFC 8832 §5.1 / §5.2 — the DCEP message wire format.** A DCEP message
  begins with a one-byte Message Type: `0x03` = DATA_CHANNEL_OPEN (followed by
  channel type, priority, reliability parameter, label length, protocol length,
  and the variable-length label and protocol), `0x02` = DATA_CHANNEL_ACK (a
  single byte). `parse` decodes exactly this.
* **RFC 8832 §6 — the open handshake.** The side opening a channel sends
  DATA_CHANNEL_OPEN on an unused stream and waits; the peer replies with
  DATA_CHANNEL_ACK on the same stream. The channel is only fully open once the
  ACK is received. `chStep` is this three-state machine.
* **RFC 8831 §6.5 / RFC 8832 §6 — stream-identifier parity.** The peers avoid
  glare by splitting the stream-id space on DTLS role: the DTLS client uses
  even stream identifiers, the DTLS server uses odd ones. The reserved id
  `65535` is never used (RFC 8831 §6.6). `streamOk` / `mayOpen` enforce this.

## The theorems

* `dcep_open_ack` — a channel reaches the `open` state only by receiving an ACK
  while in the `openSent` state; there is no other edge into `open`. So a
  channel is open only after an OPEN was sent and an ACK came back.
* `dcep_stream_parity` — a role emits a DATA_CHANNEL_OPEN only on a stream whose
  identifier matches its role parity (even for the DTLS client, odd for the
  server) and is within range.
* `parity_disjoint` — the client's even ids and the server's odd ids are
  disjoint: the two peers can never both pick the same stream identifier, so
  the parity rule removes glare by construction.

## Boundary (left uninterpreted, honestly)

The SCTP association itself (RFC 4960: the four-way INIT/COOKIE handshake, TSN
assignment, SACK-based reliability, stream reordering) and the DTLS 1.2 record
protection it runs inside (RFC 6347 / RFC 9147) are the transport/crypto
boundary. This file models the DCEP control exchange and stream-id discipline
*above* a reliable ordered stream; it does not implement SCTP chunking or DTLS.
The DTLS role that fixes the parity is an input here, not derived.
-/

namespace Dcep

/-- Raw byte strings, modeled as lists to match the sibling libraries. -/
abbrev Bytes := List UInt8

/-- Big-endian decode of two bytes. -/
def be16 (hi lo : UInt8) : Nat := hi.toNat * 256 + lo.toNat

/-- Big-endian decode of four bytes. -/
def be32 (b3 b2 b1 b0 : UInt8) : Nat :=
  ((b3.toNat * 256 + b2.toNat) * 256 + b1.toNat) * 256 + b0.toNat

/-! ## DCEP messages (RFC 8832 §5) -/

/-- A decoded DCEP message. `open` carries the §5.1 fields (channel type,
priority, reliability parameter, the label and protocol strings and their
declared lengths); `ack` is the §5.2 single-byte acknowledgement. -/
inductive Msg where
  | open (channelType priority reliability labelLen protoLen : Nat)
         (label protocol : Bytes)
  | ack
deriving Repr

/-- The DATA_CHANNEL_OPEN message type byte (RFC 8832 §8.2.1). -/
def openType : UInt8 := 0x03
/-- The DATA_CHANNEL_ACK message type byte (RFC 8832 §8.2.1). -/
def ackType : UInt8 := 0x02

/-- Parse a DCEP message (RFC 8832 §5). Dispatches on the one-byte Message Type:
`0x02` is an ACK; `0x03` is an OPEN whose 11-byte fixed part is followed by the
label and protocol, each of the declared length. Total: any other lead byte, or
an OPEN whose declared label+protocol runs past the buffer, yields `none`. -/
def parse : Bytes → Option Msg
  | b :: rest =>
    if b = ackType then
      some .ack
    else if b = openType then
      match rest with
      | ct :: p1 :: p0 :: r3 :: r2 :: r1 :: r0 :: ll1 :: ll0 :: pl1 :: pl0 :: body =>
        let labelLen := be16 ll1 ll0
        let protoLen := be16 pl1 pl0
        if labelLen + protoLen ≤ body.length then
          let label := body.take labelLen
          let protocol := (body.drop labelLen).take protoLen
          some (.open ct.toNat (be16 p1 p0) (be32 r3 r2 r1 r0) labelLen protoLen label protocol)
        else none
      | _ => none
    else none
  | [] => none

/-- **Totality.** The decoder returns for every input, either a rejection or a
single decoded message; no partial/stuck outcome. -/
theorem dcep_parse_total (b : Bytes) :
    parse b = none ∨ ∃ m, parse b = some m := by
  cases h : parse b with
  | none => exact Or.inl rfl
  | some m => exact Or.inr ⟨m, rfl⟩

/-- A parsed ACK could only have come from a message whose lead byte was
`ackType`. -/
theorem parse_ack_lead (b : Bytes) (h : parse b = some .ack) :
    ∃ rest, b = ackType :: rest := by
  match b with
  | [] => simp [parse] at h
  | c :: rest =>
    by_cases hc : c = ackType
    · exact ⟨rest, by rw [hc]⟩
    · simp only [parse, if_neg hc] at h
      by_cases ho : c = openType
      · rw [if_pos ho] at h
        -- an OPEN never decodes to `ack`
        split at h <;> · first | (split at h <;> simp_all) | simp_all
      · rw [if_neg ho] at h; simp at h

/-! ## The open handshake FSM (RFC 8832 §6) -/

/-- Channel setup state from the opener's view (RFC 8832 §6): before sending;
after sending OPEN and awaiting ACK; fully open once the ACK arrives. -/
inductive ChState where
  /-- No OPEN sent yet. -/
  | idle
  /-- OPEN sent; awaiting the ACK. -/
  | openSent
  /-- ACK received; the channel is open. -/
  | open
deriving Repr, DecidableEq

/-- The events driving channel setup. -/
inductive ChEvent where
  /-- The opener sends DATA_CHANNEL_OPEN. -/
  | sendOpen
  /-- The opener receives DATA_CHANNEL_ACK. -/
  | recvAck
deriving Repr, DecidableEq

/-- The channel-setup transition function (RFC 8832 §6). `idle` sends OPEN to
`openSent`; `openSent` receives ACK to `open`. Any other event is a no-op, and
`open` is terminal. -/
def chStep (s : ChState) (e : ChEvent) : ChState :=
  match s, e with
  | .idle,     .sendOpen => .openSent
  | .openSent, .recvAck  => .open
  | s,         _         => s

/-- **Open only after OPEN then ACK (RFC 8832 §6).** The only transition that
enters the `open` state is `recvAck` fired from `openSent`. A channel therefore
cannot be open unless an OPEN was already sent (putting it in `openSent`) and an
ACK was then received. -/
theorem dcep_open_ack (s : ChState) (e : ChEvent)
    (h : chStep s e = .open) (hne : s ≠ .open) :
    s = .openSent ∧ e = .recvAck := by
  cases s <;> cases e <;> simp_all [chStep]

/-- `open` is terminal: no event moves an open channel. -/
theorem chStep_open_terminal (e : ChEvent) : chStep .open e = .open := by
  cases e <;> rfl

/-- Sending OPEN from `idle` reaches `openSent`, never `open`: one message is not
enough. -/
theorem sendOpen_not_open : chStep .idle .sendOpen ≠ .open := by decide

/-! ## Stream-identifier parity (RFC 8831 §6.5, RFC 8832 §6) -/

/-- The DTLS role, which fixes the stream-id parity (RFC 8832 §6). -/
inductive Role where
  /-- The DTLS client: uses even stream identifiers. -/
  | dtlsClient
  /-- The DTLS server: uses odd stream identifiers. -/
  | dtlsServer
deriving Repr, DecidableEq

/-- The other peer's role. -/
def Role.peer : Role → Role
  | .dtlsClient => .dtlsServer
  | .dtlsServer => .dtlsClient

/-- Whether a stream identifier respects a role's parity (RFC 8832 §6): the DTLS
client owns the even ids, the DTLS server the odd ids. -/
def streamOk : Role → Nat → Bool
  | .dtlsClient, sid => decide (sid % 2 = 0)
  | .dtlsServer, sid => decide (sid % 2 = 1)

/-- The largest usable stream identifier: `65535` is reserved (RFC 8831 §6.6). -/
def maxStream : Nat := 65534

/-- Whether a role may open a channel on a given stream: the parity must match
and the id must be in range. -/
def mayOpen (r : Role) (sid : Nat) : Bool :=
  streamOk r sid && decide (sid ≤ maxStream)

/-- The opener's action: emit a DATA_CHANNEL_OPEN, moving to `openSent`, but
only on a stream whose id it is entitled to (correct parity, in range). An
ineligible stream produces no OPEN. -/
def openChannel (r : Role) (sid : Nat) : Option ChState :=
  if mayOpen r sid then some .openSent else none

/-- **Stream parity (RFC 8832 §6).** A role emits a DATA_CHANNEL_OPEN only on a
stream identifier that matches its parity. -/
theorem dcep_stream_parity (r : Role) (sid : Nat) (st : ChState)
    (h : openChannel r sid = some st) : streamOk r sid = true := by
  unfold openChannel at h
  by_cases hm : mayOpen r sid = true
  · unfold mayOpen at hm
    simp only [Bool.and_eq_true] at hm
    exact hm.1
  · rw [if_neg hm] at h; simp at h

/-- A role only opens within the usable stream range (never the reserved
`65535`). -/
theorem dcep_stream_in_range (r : Role) (sid : Nat) (st : ChState)
    (h : openChannel r sid = some st) : sid ≤ maxStream := by
  unfold openChannel at h
  by_cases hm : mayOpen r sid = true
  · unfold mayOpen at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    exact hm.2
  · rw [if_neg hm] at h; simp at h

/-- **Parity is disjoint.** No stream identifier is valid for both roles: the
even ids (client) and odd ids (server) never overlap, so the two peers cannot
collide on a stream number — the parity split removes glare by construction. -/
theorem parity_disjoint (sid : Nat) (h : streamOk .dtlsClient sid = true) :
    streamOk .dtlsServer sid = false := by
  simp only [streamOk, decide_eq_true_eq] at h
  simp only [streamOk, decide_eq_false_iff_not]
  omega

/-- A stream a role may open is one the *peer* must not open: `mayOpen r sid`
excludes `mayOpen r.peer sid`. The opener and responder always sit on opposite
parities. -/
theorem mayOpen_peer_excluded (r : Role) (sid : Nat) (h : mayOpen r sid = true) :
    mayOpen r.peer sid = false := by
  unfold mayOpen at *
  simp only [Bool.and_eq_true] at h
  cases r with
  | dtlsClient =>
    have := parity_disjoint sid h.1
    simp only [Role.peer, this, Bool.false_and]
  | dtlsServer =>
    -- server odd ⇒ client-parity (even) fails
    simp only [streamOk, decide_eq_true_eq] at h
    simp only [Role.peer, streamOk]
    have : ¬ (sid % 2 = 0) := by omega
    simp only [this, decide_false, Bool.false_and]

/-! ## Channel type, reliability, and priority (RFC 8832 §5.1, RFC 8831 §6.4) -/

/-- The six DCEP channel types (RFC 8832 §5.1 / §8.2.2). The high bit of the type
byte marks partial reliability; the low bit marks unordered delivery. -/
inductive ChannelType where
  /-- `0x00` DATA_CHANNEL_RELIABLE. -/
  | reliable
  /-- `0x01` DATA_CHANNEL_RELIABLE_UNORDERED. -/
  | reliableUnordered
  /-- `0x80` DATA_CHANNEL_PARTIAL_RELIABLE_REXMIT. -/
  | partialRexmit
  /-- `0x81` DATA_CHANNEL_PARTIAL_RELIABLE_REXMIT_UNORDERED. -/
  | partialRexmitUnordered
  /-- `0x82` DATA_CHANNEL_PARTIAL_RELIABLE_TIMED. -/
  | partialTimed
  /-- `0x83` DATA_CHANNEL_PARTIAL_RELIABLE_TIMED_UNORDERED. -/
  | partialTimedUnordered
deriving Repr, DecidableEq

/-- The Channel Type byte (RFC 8832 §8.2.2). -/
def ChannelType.toByte : ChannelType → UInt8
  | .reliable               => 0x00
  | .reliableUnordered      => 0x01
  | .partialRexmit          => 0x80
  | .partialRexmitUnordered => 0x81
  | .partialTimed           => 0x82
  | .partialTimedUnordered  => 0x83

/-- Decode a Channel Type byte; unassigned values are rejected. -/
def ChannelType.ofByte : UInt8 → Option ChannelType
  | 0x00 => some .reliable
  | 0x01 => some .reliableUnordered
  | 0x80 => some .partialRexmit
  | 0x81 => some .partialRexmitUnordered
  | 0x82 => some .partialTimed
  | 0x83 => some .partialTimedUnordered
  | _    => none

/-- Whether the channel type requests ordered delivery (RFC 8832 §5.1): the low
bit clear means ordered. -/
def ChannelType.ordered : ChannelType → Bool
  | .reliable | .partialRexmit | .partialTimed => true
  | _ => false

/-- Whether the channel type guarantees every message is eventually delivered
(fully reliable) — true only for the two reliable types. -/
def ChannelType.mustDeliverAll : ChannelType → Bool
  | .reliable | .reliableUnordered => true
  | _ => false

/-- The reliability regime a channel selects (RFC 8832 §5.1). -/
inductive Reliability where
  /-- Deliver every message; unbounded retransmission. -/
  | fullyReliable
  /-- Give up on a message after `maxRexmit` retransmissions. -/
  | partialRexmit (maxRexmit : Nat)
  /-- Give up on a message after `lifetimeMs` milliseconds. -/
  | partialTimed (lifetimeMs : Nat)
deriving Repr, DecidableEq

/-- Interpret the 32-bit Reliability Parameter under a channel type (RFC 8832
§5.1): ignored for the reliable types, a max-retransmit count for the rexmit
types, a max-lifetime-in-ms for the timed types. -/
def ChannelType.reliabilityOf (ct : ChannelType) (param : Nat) : Reliability :=
  match ct with
  | .reliable | .reliableUnordered               => .fullyReliable
  | .partialRexmit | .partialRexmitUnordered      => .partialRexmit param
  | .partialTimed | .partialTimedUnordered        => .partialTimed param

/-- **Channel-type byte round-trips (RFC 8832 §8.2.2).** Encoding a channel type
and decoding the byte recovers it — the type codes are a faithful injection into
the byte space. -/
theorem channelType_byte_roundtrip (ct : ChannelType) :
    ChannelType.ofByte ct.toByte = some ct := by
  cases ct <;> rfl

/-- **A fully-reliable channel is exactly a must-deliver-all channel.** The
reliability regime and the delivery guarantee agree: a channel delivers every
message iff its regime is `fullyReliable`, for any reliability parameter. -/
theorem mustDeliver_iff_fullyReliable (ct : ChannelType) (param : Nat) :
    ct.mustDeliverAll = true ↔ ct.reliabilityOf param = .fullyReliable := by
  cases ct <;> simp [ChannelType.mustDeliverAll, ChannelType.reliabilityOf]

/-- The reliable ordered channel is ordered, must deliver all, and is fully
reliable — the WebRTC default data-channel profile (RFC 8831 §6.2). -/
theorem reliable_profile :
    ChannelType.reliable.ordered = true ∧
    ChannelType.reliable.mustDeliverAll = true ∧
    (∀ param, ChannelType.reliable.reliabilityOf param = .fullyReliable) := by
  refine ⟨rfl, rfl, ?_⟩; intro _; rfl

/-! ## Channel priority (RFC 8831 §6.4) -/

/-- The four recommended data-channel priority levels (RFC 8831 §6.4). The wire
Priority field is a 16-bit unsigned integer; these are the interoperable values
a WebRTC stack uses. -/
inductive PriorityLevel where
  | belowNormal
  | normal
  | high
  | extraHigh
deriving Repr, DecidableEq

/-- The wire value of a priority level (RFC 8831 §6.4). -/
def PriorityLevel.value : PriorityLevel → Nat
  | .belowNormal => 128
  | .normal      => 256
  | .high        => 512
  | .extraHigh   => 1024

/-- **The priority levels are strictly ordered (RFC 8831 §6.4).** Higher levels
carry strictly larger wire values, so a scheduler comparing the raw 16-bit field
orders channels the way the level names intend. -/
theorem priority_levels_ordered :
    PriorityLevel.belowNormal.value < PriorityLevel.normal.value ∧
    PriorityLevel.normal.value < PriorityLevel.high.value ∧
    PriorityLevel.high.value < PriorityLevel.extraHigh.value := by
  decide

/-! ## The channel configuration carried by a DATA_CHANNEL_OPEN (RFC 8832 §5.1) -/

/-- The semantic configuration a DATA_CHANNEL_OPEN establishes: the channel
type, its derived ordering and reliability regime, and its priority. -/
structure ChannelConfig where
  channelType : ChannelType
  ordered : Bool
  reliability : Reliability
  priority : Nat
deriving Repr

/-- Derive the channel configuration from a parsed DCEP message (RFC 8832 §5.1).
An ACK carries no configuration; an OPEN whose channel-type byte is unassigned is
rejected. -/
def configOf : Msg → Option ChannelConfig
  | .open ct priority reliability _ _ _ _ =>
      match ChannelType.ofByte (UInt8.ofNat ct) with
      | some cty =>
          some { channelType := cty
               , ordered := cty.ordered
               , reliability := cty.reliabilityOf reliability
               , priority := priority }
      | none => none
  | .ack => none

/-- An ACK never yields a channel configuration. -/
theorem configOf_ack : configOf .ack = none := rfl

/-- **The derived configuration is internally consistent (RFC 8832 §5.1).** The
`ordered` flag of any configuration `configOf` produces is exactly the ordering
its channel type dictates — the parser never records an ordering at odds with the
channel type. -/
theorem configOf_ordered_consistent (m : Msg) (cfg : ChannelConfig)
    (h : configOf m = some cfg) : cfg.ordered = cfg.channelType.ordered := by
  cases m with
  | ack => simp [configOf] at h
  | «open» ct priority reliability labelLen protoLen label protocol =>
      simp only [configOf] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · simp at h

/-- The reliability regime a configuration records is the one its channel type
selects from the message's Reliability Parameter. -/
theorem configOf_reliability_consistent (m : Msg) (cfg : ChannelConfig)
    (h : configOf m = some cfg) :
    ∃ param, cfg.reliability = cfg.channelType.reliabilityOf param := by
  cases m with
  | ack => simp [configOf] at h
  | «open» ct priority reliability labelLen protoLen label protocol =>
      simp only [configOf] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨reliability, rfl⟩
      · simp at h

def version : String := "0.1.0"

end Dcep
