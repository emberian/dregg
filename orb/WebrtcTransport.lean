import Crypto

/-!
# WebRTC transport: DTLS 1.3, SCTP association, and ordered data-channel delivery

A total, sans-IO model of the three layers a WebRTC data channel rides on once
ICE (`Ice.lean`) has nominated a candidate pair: the DTLS 1.3 handshake that
protects the flow (RFC 9147), the SCTP association it multiplexes over
(RFC 4960 §5.1), and the reliable/ordered delivery the data channel presents to
the application (RFC 8831). Each layer is a total transition system or a pure
function with real theorems; the cryptography is the verified EverCrypt boundary
of `Crypto.lean` (HACL*/EverCrypt), used for real here — the DTLS key schedule
runs HKDF and record protection runs the AEAD, not a stub.

## What this file captures

* **RFC 9147 §5 — the DTLS 1.3 handshake FSM.** The client walks
  `start → wait_sh → wait_finished → established`: it sends its ClientHello,
  receives the ServerHello (after which handshake keys exist), then completes
  the Finished exchange (after which application traffic keys exist). Only in
  `established` may application data be protected or accepted. `dtlsStep` is
  this graph and `sealAppData` / `openAppData` are the gate.
* **RFC 9147 §5.2 / RFC 8446 §7.1 — the key schedule.** `deriveHandshakeKeys`
  and `deriveAppKeys` run HKDF-Extract then HKDF-Expand over the (EC)DHE shared
  secret, calling `Crypto.hkdfExtract` / `Crypto.hkdfExpand` (EverCrypt). Record
  protection is `Crypto.chachaSeal` / `Crypto.chachaOpen`.
* **RFC 4960 §5.1 — the SCTP four-way association setup.** The client walks
  `closed → cookieWait → cookieEchoed → established` by
  INIT / INIT-ACK / COOKIE-ECHO / COOKIE-ACK. User data may be transferred only
  once `established`. `sctpStep` is the graph; a rank argument proves it takes at
  least the three transitions of the four-way exchange.
* **RFC 8831 §6.6 — ordered delivery.** An `OrdRecv` receiver holds
  out-of-order chunks in a reorder buffer and releases a maximal run of
  consecutive stream-sequence numbers starting at the next expected one.
  `flush` is that release; it delivers strictly increasing, gap-free sequence
  numbers.

## The theorems

* `dtls_no_appdata_before_established` — `sealAppData` yields a protected record
  only in the `established` state; no application data is protected before the
  handshake completes. `dtls_appdata_authentic` composes with the EverCrypt AEAD
  authenticity axiom: any accepted record's plaintext is exactly what the peer
  sealed.
* `sctp_assoc_4way` — reaching `established` from `closed` takes at least three
  state transitions (the INIT/INIT-ACK/COOKIE-ECHO/COOKIE-ACK four-way exchange).
  `sctp_data_after_established` gates user data on `established`.
* `datachannel_ordered` — the stream-sequence numbers a receive step releases
  are strictly increasing (`StrictSorted`); in fact `datachannel_consecutive`
  shows they are gap-free from the next expected number, so ordered delivery
  preserves the sender's sequence. `datachannel_nextSsn_mono` — the delivery
  pointer never rewinds.

## Boundary (left uninterpreted, honestly)

The (EC)DHE key exchange that produces the DTLS shared secret is `Crypto.x25519`
(the shared-secret agreement is `Crypto.Assumptions.x25519_dh_agree`); the
certificate/transcript authentication of the handshake, DTLS record replay
windows and epoch bookkeeping, and the SCTP congestion/retransmission timers and
TSN/SACK reliability are outside this model — it captures the state gating and
the ordered-delivery discipline above a lossy reorder buffer, with the crypto
seam bound to the verified primitives.
-/

namespace WebrtcTransport

/-- Raw byte strings, modeled as lists to match the sibling libraries. The FFI
crypto boundary works on `ByteArray`; conversion is `⟨l.toArray⟩` / `.toList`. -/
abbrev Bytes := List UInt8

/-! ## The DTLS 1.3 handshake FSM (RFC 9147 §5) -/

/-- DTLS 1.3 handshake state from the client's view (RFC 9147 §5.1). -/
inductive DtlsState where
  /-- Nothing sent yet. -/
  | start
  /-- ClientHello sent; awaiting ServerHello. -/
  | wait_sh
  /-- ServerHello received (handshake keys exist); awaiting/serving the
  Finished exchange. -/
  | wait_finished
  /-- Finished exchange complete; application traffic keys exist. Terminal for
  the handshake — application data flows only here. -/
  | established
  /-- Connection closed (close_notify). -/
  | closed
deriving Repr, DecidableEq

/-- The events driving the handshake. `recvFinished` bundles the client's
receipt of the server Finished and the send of its own Finished (RFC 9147 §5),
after which the connection is established. -/
inductive DtlsEvent where
  | sendClientHello
  | recvServerHello
  | recvFinished
  | close
deriving Repr, DecidableEq

/-- The DTLS handshake transition function (RFC 9147 §5). Any event not drawn on
the current state is a no-op; `close` ends the connection from anywhere. -/
def dtlsStep : DtlsState → DtlsEvent → DtlsState
  | .start,         .sendClientHello => .wait_sh
  | .wait_sh,       .recvServerHello => .wait_finished
  | .wait_finished, .recvFinished    => .established
  | _,              .close           => .closed
  | s,              _                => s

/-- The only edge into `established` is `recvFinished` fired from
`wait_finished`: the handshake cannot complete without a ServerHello (reaching
`wait_finished`) and then the Finished exchange. -/
theorem dtls_enter_established (s : DtlsState) (e : DtlsEvent)
    (h : dtlsStep s e = .established) (hne : s ≠ .established) :
    s = .wait_finished ∧ e = .recvFinished := by
  cases s <;> cases e <;> simp_all [dtlsStep]

/-! ## The DTLS 1.3 key schedule (RFC 9147 §5.2, RFC 8446 §7.1)

Real EverCrypt HKDF over the (EC)DHE shared secret. Labels follow the TLS 1.3
key-schedule shape; the exact label bytes are not load-bearing for the theorems
(the gate is structural), but the derivation is a genuine HKDF call, not a stub. -/

/-- The client application-traffic-secret label (RFC 8446 §7.1). -/
def clientAppLabel : ByteArray := "c ap traffic".toUTF8
/-- The server application-traffic-secret label. -/
def serverAppLabel : ByteArray := "s ap traffic".toUTF8
/-- The client/server handshake-traffic-secret labels. -/
def clientHsLabel : ByteArray := "c hs traffic".toUTF8
def serverHsLabel : ByteArray := "s hs traffic".toUTF8

/-- A directional AEAD key pair for a DTLS epoch. -/
structure Keys where
  clientKey : ByteArray
  serverKey : ByteArray

/-- Derive the DTLS handshake-epoch keys from the (EC)DHE shared secret via
HKDF (EverCrypt): Extract with the transcript-derived salt, then Expand per
direction. `none` on a size mismatch at the crypto boundary. -/
def deriveHandshakeKeys (sharedSecret salt : ByteArray) : Option Keys := do
  let prk ← Crypto.hkdfExtract salt sharedSecret
  let ck ← Crypto.hkdfExpand prk clientHsLabel 32
  let sk ← Crypto.hkdfExpand prk serverHsLabel 32
  some { clientKey := ck, serverKey := sk }

/-- Derive the DTLS application-epoch traffic keys from the master secret via
HKDF (EverCrypt). Available only after the Finished exchange (`established`). -/
def deriveAppKeys (masterSecret salt : ByteArray) : Option Keys := do
  let prk ← Crypto.hkdfExtract salt masterSecret
  let ck ← Crypto.hkdfExpand prk clientAppLabel 32
  let sk ← Crypto.hkdfExpand prk serverAppLabel 32
  some { clientKey := ck, serverKey := sk }

/-! ## Application-data record protection, gated on `established` -/

/-- Protect one application-data record (RFC 9147 §4): AEAD-seal with EverCrypt
ChaCha20-Poly1305 — but only in the `established` state. Before the handshake
completes there is no application epoch, so no record is produced. -/
def sealAppData (st : DtlsState) (key nonce ad msg : ByteArray) : Option ByteArray :=
  if st = .established then Crypto.chachaSeal key nonce ad msg else none

/-- Accept one inbound application-data record: AEAD-open with EverCrypt — only
in the `established` state. -/
def openAppData (st : DtlsState) (key nonce ad ct : ByteArray) : Option ByteArray :=
  if st = .established then Crypto.chachaOpen key nonce ad ct else none

/-- **No application data before established (RFC 9147 §5).** A protected record
is produced only in the `established` state, so no application data crosses the
DTLS layer before the handshake completes. -/
theorem dtls_no_appdata_before_established
    (st : DtlsState) (key nonce ad msg ct : ByteArray)
    (h : sealAppData st key nonce ad msg = some ct) : st = .established := by
  unfold sealAppData at h
  by_cases hs : st = .established
  · exact hs
  · rw [if_neg hs] at h; simp at h

/-- Symmetrically, an inbound record is accepted only in `established`. -/
theorem dtls_no_recv_before_established
    (st : DtlsState) (key nonce ad ct msg : ByteArray)
    (h : openAppData st key nonce ad ct = some msg) : st = .established := by
  unfold openAppData at h
  by_cases hs : st = .established
  · exact hs
  · rw [if_neg hs] at h; simp at h

/-- **Accepted records are authentic (EverCrypt AEAD).** Composing the DTLS gate
with `Crypto.Assumptions.chacha_open_authentic`: any application record the DTLS
layer accepts was sealed by the peer under this exact key/nonce/ad for exactly
this plaintext — no attacker-fabricated record is ever surfaced. This is the
conditional security guarantee, relative to the EverCrypt authenticity axiom. -/
theorem dtls_appdata_authentic
    (st : DtlsState) (key nonce ad ct msg : ByteArray)
    (h : openAppData st key nonce ad ct = some msg) :
    st = .established ∧ Crypto.chachaSeal key nonce ad msg = some ct := by
  unfold openAppData at h
  by_cases hs : st = .established
  · rw [if_pos hs] at h
    exact ⟨hs, Crypto.Assumptions.chacha_open_authentic key nonce ad ct msg h⟩
  · rw [if_neg hs] at h; simp at h

/-! ## SCTP association establishment (RFC 4960 §5.1, four-way) -/

/-- SCTP association state from the initiator's view (RFC 4960 §4). -/
inductive SctpState where
  /-- No association. -/
  | closed
  /-- INIT sent; awaiting INIT-ACK. -/
  | cookieWait
  /-- COOKIE-ECHO sent; awaiting COOKIE-ACK. -/
  | cookieEchoed
  /-- COOKIE-ACK received; the association is up. User data flows only here. -/
  | established
  /-- Association torn down. -/
  | shutdown
deriving Repr, DecidableEq

/-- The events of the four-way exchange (RFC 4960 §5.1). -/
inductive SctpEvent where
  /-- Send INIT. -/
  | sendInit
  /-- Receive INIT-ACK (and send COOKIE-ECHO). -/
  | recvInitAck
  /-- Receive COOKIE-ACK. -/
  | recvCookieAck
  /-- Abort/shutdown. -/
  | shutdownEv
deriving Repr, DecidableEq

/-- The SCTP association transition function (RFC 4960 §5.1). -/
def sctpStep : SctpState → SctpEvent → SctpState
  | .closed,       .sendInit      => .cookieWait
  | .cookieWait,   .recvInitAck   => .cookieEchoed
  | .cookieEchoed, .recvCookieAck => .established
  | _,             .shutdownEv    => .shutdown
  | s,             _              => s

/-- The only edge into `established` is `recvCookieAck` fired from
`cookieEchoed`: the association cannot come up without the COOKIE-ACK that
closes the four-way exchange. -/
theorem sctp_enter_established (s : SctpState) (e : SctpEvent)
    (h : sctpStep s e = .established) (hne : s ≠ .established) :
    s = .cookieEchoed ∧ e = .recvCookieAck := by
  cases s <;> cases e <;> simp_all [sctpStep]

/-- Progress rank of the setup handshake: each of the three four-way transitions
advances it by one; `established` sits at rank `3`. -/
def sctpRank : SctpState → Nat
  | .closed       => 0
  | .cookieWait   => 1
  | .cookieEchoed => 2
  | .established  => 3
  | .shutdown     => 0

/-- A single transition advances the setup rank by at most one. -/
theorem sctpStep_rank_incr (s : SctpState) (e : SctpEvent) :
    sctpRank (sctpStep s e) ≤ sctpRank s + 1 := by
  cases s <;> cases e <;> decide

/-- Fold the transition function over an event trace. -/
def sctpRun : SctpState → List SctpEvent → SctpState
  | s, []      => s
  | s, e :: es => sctpRun (sctpStep s e) es

/-- Over a trace, the setup rank grows by at most the trace length. -/
theorem sctpRun_rank_bound (s : SctpState) (es : List SctpEvent) :
    sctpRank (sctpRun s es) ≤ sctpRank s + es.length := by
  induction es generalizing s with
  | nil => simp [sctpRun]
  | cons e es ih =>
    simp only [sctpRun, List.length_cons]
    calc sctpRank (sctpRun (sctpStep s e) es)
          ≤ sctpRank (sctpStep s e) + es.length := ih _
      _ ≤ (sctpRank s + 1) + es.length := by have := sctpStep_rank_incr s e; omega
      _ = sctpRank s + (es.length + 1) := by omega

/-- **The four-way exchange (RFC 4960 §5.1).** Bringing an SCTP association from
`closed` to `established` takes at least three state transitions — the
INIT / INIT-ACK / COOKIE-ECHO / COOKIE-ACK four-way handshake. No shorter trace
establishes the association. -/
theorem sctp_assoc_4way (es : List SctpEvent)
    (h : sctpRun .closed es = .established) : 3 ≤ es.length := by
  have hb := sctpRun_rank_bound .closed es
  rw [h] at hb
  simp only [sctpRank] at hb
  omega

/-- Whether user data may be transferred: only on an established association. -/
def sctpMayXfer (st : SctpState) : Bool := decide (st = .established)

/-- **User data only after COOKIE-ACK (RFC 4960 §5.1).** The data-transfer gate
opens only in the `established` state. -/
theorem sctp_data_after_established (st : SctpState) (h : sctpMayXfer st = true) :
    st = .established := by
  unfold sctpMayXfer at h
  exact of_decide_eq_true h

/-! ## Ordered data-channel delivery (RFC 8831 §6.6)

An ordered stream reassembles by stream-sequence number (SSN): the receiver
delivers a maximal run of consecutive SSNs starting at the next expected one and
holds any out-of-order chunk in a reorder buffer until its predecessors arrive. -/

/-- A reassembled application chunk carrying its SSN. -/
structure Chunk where
  ssn : Nat
  payload : Bytes
deriving Repr

/-- A list of naturals is strictly increasing. Self-contained (no Mathlib). -/
def StrictSorted : List Nat → Prop
  | []          => True
  | [_]         => True
  | a :: b :: r => a < b ∧ StrictSorted (b :: r)

/-- A list of naturals is exactly `start, start+1, start+2, …` — gap-free and
increasing. This is the sharp "ordered delivery preserves the sequence" shape. -/
def Consecutive (start : Nat) : List Nat → Prop
  | []      => True
  | a :: rest => a = start ∧ Consecutive (start + 1) rest

/-- A consecutive run is strictly sorted. -/
theorem consecutive_strictSorted :
    ∀ (start : Nat) (l : List Nat), Consecutive start l → StrictSorted l
  | _, [],       _ => trivial
  | _, [_],      _ => trivial
  | start, a :: b :: rest, h => by
      simp only [Consecutive] at h
      obtain ⟨ha, hbc⟩ := h
      have hb : b = start + 1 := hbc.1
      show a < b ∧ StrictSorted (b :: rest)
      exact ⟨by omega, consecutive_strictSorted (start + 1) (b :: rest) hbc⟩

/-- Release a maximal run of consecutive SSNs from the reorder buffer, starting
at `next`. Structurally recursive on `fuel` (the buffer length suffices, since
each release removes one chunk). Returns the new next-expected SSN, the released
chunks in order, and the remaining buffer. -/
def flush : Nat → List Chunk → Nat → Nat × List Chunk × List Chunk
  | next, buf, 0 => (next, [], buf)
  | next, buf, fuel + 1 =>
    match buf.find? (fun c => c.ssn == next) with
    | some c =>
        let buf' := buf.filter (fun c => c.ssn != next)
        let r := flush (next + 1) buf' fuel
        (r.1, c :: r.2.1, r.2.2)
    | none => (next, [], buf)

/-- The next-expected SSN never rewinds under `flush`. -/
theorem flush_next_ge (next : Nat) (buf : List Chunk) (fuel : Nat) :
    next ≤ (flush next buf fuel).1 := by
  induction fuel generalizing next buf with
  | zero => simp [flush]
  | succ fuel ih =>
    unfold flush
    cases hf : buf.find? (fun c => c.ssn == next) with
    | none => simp
    | some c =>
        show next ≤ (flush (next + 1) (buf.filter (fun c => c.ssn != next)) fuel).1
        have := ih (next + 1) (buf.filter (fun c => c.ssn != next)); omega

/-- **The released run is gap-free and increasing (RFC 8831 §6.6).** Whatever the
reorder buffer holds, the SSNs `flush` releases are exactly `next, next+1, …`. -/
theorem flush_consecutive (next : Nat) (buf : List Chunk) (fuel : Nat) :
    Consecutive next ((flush next buf fuel).2.1.map (·.ssn)) := by
  induction fuel generalizing next buf with
  | zero => simp [flush, Consecutive]
  | succ fuel ih =>
    unfold flush
    cases hf : buf.find? (fun c => c.ssn == next) with
    | none => trivial
    | some c =>
        have hcssn : c.ssn = next :=
          Nat.eq_of_beq_eq_true (by simpa using List.find?_some hf)
        show Consecutive next
          ((c :: (flush (next + 1) (buf.filter (fun c => c.ssn != next)) fuel).2.1).map (·.ssn))
        simp only [List.map_cons, Consecutive]
        exact ⟨hcssn, ih (next + 1) (buf.filter (fun c => c.ssn != next))⟩

/-- The reorder-buffer receiver: the next-expected SSN and the held chunks. -/
structure OrdRecv where
  nextSsn : Nat
  buf : List Chunk

/-- Receive a chunk (RFC 8831 §6.6). A chunk older than `nextSsn` is a duplicate
and dropped. Otherwise it is buffered and a maximal consecutive run is released. -/
def OrdRecv.recv (r : OrdRecv) (c : Chunk) : OrdRecv × List Chunk :=
  if c.ssn < r.nextSsn then
    (r, [])
  else
    let buf0 := c :: r.buf
    let res := flush r.nextSsn buf0 buf0.length
    ({ nextSsn := res.1, buf := res.2.2 }, res.2.1)

/-- **Ordered delivery preserves the sequence (RFC 8831 §6.6).** The SSNs a
receive step releases are strictly increasing — no reordering, no duplicates. -/
theorem datachannel_ordered (r : OrdRecv) (c : Chunk) :
    StrictSorted ((r.recv c).2.map (·.ssn)) := by
  unfold OrdRecv.recv
  by_cases h : c.ssn < r.nextSsn
  · rw [if_pos h]; simp [StrictSorted]
  · rw [if_neg h]
    show StrictSorted ((flush r.nextSsn (c :: r.buf) (c :: r.buf).length).2.1.map (·.ssn))
    exact consecutive_strictSorted _ _ (flush_consecutive r.nextSsn (c :: r.buf) (c :: r.buf).length)

/-- The stronger statement: the released SSNs are gap-free from `nextSsn`. -/
theorem datachannel_consecutive (r : OrdRecv) (c : Chunk) (h : ¬ c.ssn < r.nextSsn) :
    Consecutive r.nextSsn ((r.recv c).2.map (·.ssn)) := by
  unfold OrdRecv.recv
  rw [if_neg h]
  show Consecutive r.nextSsn ((flush r.nextSsn (c :: r.buf) (c :: r.buf).length).2.1.map (·.ssn))
  exact flush_consecutive r.nextSsn (c :: r.buf) (c :: r.buf).length

/-- **The delivery pointer never rewinds.** A receive step never lowers the
next-expected SSN, so ordered delivery only ever advances. -/
theorem datachannel_nextSsn_mono (r : OrdRecv) (c : Chunk) :
    r.nextSsn ≤ (r.recv c).1.nextSsn := by
  unfold OrdRecv.recv
  by_cases h : c.ssn < r.nextSsn
  · rw [if_pos h]; exact Nat.le_refl _
  · rw [if_neg h]
    show r.nextSsn ≤ (flush r.nextSsn (c :: r.buf) (c :: r.buf).length).1
    exact flush_next_ge r.nextSsn (c :: r.buf) (c :: r.buf).length

def version : String := "0.1.0"

end WebrtcTransport
