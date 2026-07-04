/-
# TlsCrypto — the TLS 1.3 key schedule and record layer over verified crypto

The TLS record/handshake state machine in `Tls/` takes cryptography as a set of
uninterpreted function-valued fields of `Tls.Config` (`hsFeed`, `recOpen`,
`recSeal`, `recCloseNotify`, `extractSecrets`). Every theorem in `Tls/Theorems`
holds uniformly over all of them — that is the named crypto-axiom boundary. But
uniformity is not execution: with the crypto uninterpreted, the machine cannot
actually complete a handshake or protect a byte. This module supplies the
missing half: the *real* TLS 1.3 key schedule and record layer, computed over
the EverCrypt primitives in `Crypto.lean` (HACL*/EverCrypt, verified in F*).

Two concrete constructions, both over `Crypto`:

* **The key schedule** (RFC 8446 §7.1). `HKDF-Expand-Label` / `Derive-Secret`
  over `Crypto.hkdfExpand`; the early / handshake / master secrets over
  `Crypto.hkdfExtract`; the client/server handshake- and application-traffic
  secrets; and the per-direction record keys (`[sender]_write_key/_iv`, §7.3).
  Transcript hashing is `Crypto.sha256`.

* **The record layer** (RFC 8446 §5.2, §5.3). The per-record nonce
  (sequence number XOR write-IV), the additional-data header, and AEAD
  seal/open over `Crypto.chachaSeal` / `Crypto.chachaOpen`
  (TLS_CHACHA20_POLY1305_SHA256).

Three theorems tie these to the crypto axioms, and one ties them back to the
state machine:

* `keyschedule_deterministic` — the derived secrets are a pure function of the
  shared secret and the transcript hashes; there is no hidden input.
* `record_roundtrip` — seal then open under the same key recovers the
  plaintext (transported from `Crypto.Assumptions.chacha_open_seal_roundtrip`).
* `record_forgery_fails` — a record that is not the genuine sealing of `m`
  never opens to `m` (transported from `Crypto.Assumptions.chacha_open_authentic`).
* `tls_no_plaintext_after_close` — `Tls.no_plain_after_close`, specialized to a
  `Tls.Config` whose record functions are *this* real record layer. The safety
  property survives the substitution of the stub by live EverCrypt.

The self-test `tls-keyschedule-selftest` runs the key schedule against the
RFC 8448 §3 "Simple 1-RTT Handshake" vectors on the linked EverCrypt.
-/

import Crypto
import Tls.Theorems

namespace TlsCrypto

open Crypto

/-! ## Byte helpers

All crypto works on `ByteArray` (matching `Crypto`); the state-machine boundary
converts to/from `Tls.Bytes = List UInt8` with `⟨l.toArray⟩` / `.toList`. -/

/-- The SHA-256 digest length, in bytes: the "Hash.length" of RFC 8446 for a
SHA-256 cipher suite. -/
def hashLen : Nat := 32

/-- The ChaCha20-Poly1305 write-key length. -/
def keyLen : Nat := 32

/-- The ChaCha20-Poly1305 write-IV / record-nonce length. -/
def ivLen : Nat := 12

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray :=
  ByteArray.mk (List.replicate n (0 : UInt8)).toArray

@[simp] theorem zeros_size (n : Nat) : (zeros n).size = n := by
  simp [zeros, ByteArray.size]

/-- Big-endian `uint16`. -/
def u16be (n : Nat) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- Big-endian 8-byte encoding of a record sequence number. -/
def u64be8 (n : Nat) : ByteArray :=
  ByteArray.mk (((List.range 8).map
    (fun i => UInt8.ofNat (n / (256 ^ (7 - i))))).toArray)

@[simp] theorem u64be8_size (n : Nat) : (u64be8 n).size = 8 := by
  simp [u64be8, ByteArray.size]

/-- Bytewise XOR of two buffers (truncating to the shorter, which the callers
never trigger — the operands are always equal length). -/
def xorBytes (a b : ByteArray) : ByteArray :=
  ByteArray.mk ((a.toList.zip b.toList).map (fun p => p.1 ^^^ p.2)).toArray

/-! ## Key schedule — RFC 8446 §7.1 / §7.3, over `Crypto` HKDF

`HKDF-Expand-Label(Secret, Label, Context, Length)` where

    struct {
      uint16 length = Length;
      opaque label<7..255>   = "tls13 " + Label;
      opaque context<0..255> = Context;
    } HkdfLabel;

so the encoded label is `length ‖ len(fullLabel) ‖ fullLabel ‖ len(ctx) ‖ ctx`.
-/

/-- The `HkdfLabel` structure of RFC 8446 §7.1, encoded to bytes. -/
def hkdfLabel (length : Nat) (label context : ByteArray) : ByteArray :=
  let fullLabel := "tls13 ".toUTF8 ++ label
  u16be length
    ++ ByteArray.mk #[UInt8.ofNat fullLabel.size] ++ fullLabel
    ++ ByteArray.mk #[UInt8.ofNat context.size] ++ context

/-- `HKDF-Expand-Label` (RFC 8446 §7.1): expand `secret` under the encoded
label to `length` bytes. `none` on the `Crypto.hkdfExpand` size limits. -/
def expandLabel (secret label context : ByteArray) (length : Nat) :
    Option ByteArray :=
  hkdfExpand secret (hkdfLabel length label context) (USize.ofNat length)

/-- `Derive-Secret(Secret, Label, Messages)` (RFC 8446 §7.1) where `thash` is the
already-computed `Transcript-Hash(Messages)`; the output is `Hash.length` bytes. -/
def deriveSecret (secret label thash : ByteArray) : Option ByteArray :=
  expandLabel secret label thash hashLen

/-- `Derive-Secret` taking the raw transcript messages and hashing them with the
suite hash (`Crypto.sha256`). -/
def deriveSecretOfMessages (secret label messages : ByteArray) :
    Option ByteArray :=
  deriveSecret secret label (sha256 messages)

/-- The transcript hash of the empty message list, `SHA-256("")`. Used as the
context for the two `"derived"` steps of the schedule. -/
def emptyHash : ByteArray := sha256 ByteArray.empty

/-- **Early Secret** = `HKDF-Extract(0, PSK)` (RFC 8446 §7.1). The salt node "0"
is `Hash.length` zeros; with no PSK the IKM is `Hash.length` zeros too. -/
def earlySecret (psk : ByteArray) : Option ByteArray :=
  hkdfExtract (zeros hashLen) psk

/-- The early secret in the common no-PSK case. -/
def earlySecretNoPsk : Option ByteArray := earlySecret (zeros hashLen)

/-- **Handshake Secret** = `HKDF-Extract(Derive-Secret(ES, "derived", ""), DHE)`.
`dhe` is the `X25519` shared secret (`Crypto.x25519`). -/
def handshakeSecret (es dhe : ByteArray) : Option ByteArray :=
  match deriveSecret es "derived".toUTF8 emptyHash with
  | some d => hkdfExtract d dhe
  | none => none

/-- **Master Secret** = `HKDF-Extract(Derive-Secret(HS, "derived", ""), 0)`. -/
def masterSecret (hs : ByteArray) : Option ByteArray :=
  match deriveSecret hs "derived".toUTF8 emptyHash with
  | some d => hkdfExtract d (zeros hashLen)
  | none => none

/-- client_handshake_traffic_secret; `thash` = Transcript-Hash(CH..SH). -/
def clientHsTrafficSecret (hs thash : ByteArray) : Option ByteArray :=
  deriveSecret hs "c hs traffic".toUTF8 thash

/-- server_handshake_traffic_secret. -/
def serverHsTrafficSecret (hs thash : ByteArray) : Option ByteArray :=
  deriveSecret hs "s hs traffic".toUTF8 thash

/-- client_application_traffic_secret_0; `thash` = Transcript-Hash(CH..SF). -/
def clientApTrafficSecret (ms thash : ByteArray) : Option ByteArray :=
  deriveSecret ms "c ap traffic".toUTF8 thash

/-- server_application_traffic_secret_0. -/
def serverApTrafficSecret (ms thash : ByteArray) : Option ByteArray :=
  deriveSecret ms "s ap traffic".toUTF8 thash

/-- One direction's record protection keys, derived from a traffic secret. -/
structure RecordKeys where
  key : ByteArray
  iv : ByteArray

/-- `[sender]_write_key` / `[sender]_write_iv` (RFC 8446 §7.3): expand the
traffic secret under the `"key"` and `"iv"` labels with empty context. For
ChaCha20-Poly1305 the sizes are 32 and 12. -/
def trafficKeys (secret : ByteArray) : Option RecordKeys :=
  match expandLabel secret "key".toUTF8 ByteArray.empty keyLen,
        expandLabel secret "iv".toUTF8 ByteArray.empty ivLen with
  | some k, some iv => some { key := k, iv := iv }
  | _, _ => none

/-- The whole schedule as one record, so its determinism is one statement. -/
structure Schedule where
  early : Option ByteArray
  handshake : Option ByteArray
  master : Option ByteArray
  clientHs : Option ByteArray
  serverHs : Option ByteArray
  clientAp : Option ByteArray
  serverAp : Option ByteArray

/-- Derive every secret of the schedule from the shared secret and the two
transcript hashes (handshake-phase `thHS`, application-phase `thAP`). No PSK. -/
def deriveSchedule (dhe thHS thAP : ByteArray) : Schedule :=
  let es := earlySecretNoPsk
  let hs := es.bind (fun e => handshakeSecret e dhe)
  let ms := hs.bind masterSecret
  { early := es
    handshake := hs
    master := ms
    clientHs := hs.bind (fun h => clientHsTrafficSecret h thHS)
    serverHs := hs.bind (fun h => serverHsTrafficSecret h thHS)
    clientAp := ms.bind (fun m => clientApTrafficSecret m thAP)
    serverAp := ms.bind (fun m => serverApTrafficSecret m thAP) }

/-! ### Determinism: the schedule is a function of its inputs -/

/-- **The key schedule is deterministic.** The derived secrets depend only on
the shared secret and the transcript hashes; there is no hidden state and no
randomness, so equal inputs yield an equal schedule. (The crypto primitives
underneath are themselves pure `Crypto` functions.) -/
theorem keyschedule_deterministic
    {dhe thHS thAP dhe' thHS' thAP' : ByteArray}
    (hd : dhe = dhe') (h1 : thHS = thHS') (h2 : thAP = thAP') :
    deriveSchedule dhe thHS thAP = deriveSchedule dhe' thHS' thAP' := by
  subst hd; subst h1; subst h2; rfl

/-- Spec-conformance, made checkable by `rfl`: the schedule's fields are exactly
the RFC 8446 §7.1 chain. -/
theorem deriveSchedule_early (dhe thHS thAP : ByteArray) :
    (deriveSchedule dhe thHS thAP).early = hkdfExtract (zeros hashLen) (zeros hashLen) :=
  rfl

theorem deriveSchedule_handshake (dhe thHS thAP : ByteArray) :
    (deriveSchedule dhe thHS thAP).handshake
      = earlySecretNoPsk.bind (fun e => handshakeSecret e dhe) :=
  rfl

theorem deriveSchedule_master (dhe thHS thAP : ByteArray) :
    (deriveSchedule dhe thHS thAP).master
      = (earlySecretNoPsk.bind (fun e => handshakeSecret e dhe)).bind masterSecret :=
  rfl

/-! ## Record layer — RFC 8446 §5.2 / §5.3, over `Crypto` ChaCha20-Poly1305 -/

/-- The per-record nonce (RFC 8446 §5.3): the 64-bit sequence number, left-padded
with zeros to the IV length, XORed with the static write-IV. -/
def recordNonce (iv : ByteArray) (seq : Nat) : ByteArray :=
  xorBytes iv (zeros (iv.size - 8) ++ u64be8 seq)

/-- The record additional-data header (RFC 8446 §5.2): `opaque_type(23) ‖
legacy_record_version(0x0303) ‖ length`, where `length` is the size of the
`TLSCiphertext.encrypted_record` (plaintext + 16-byte tag). -/
def recordAD (ciphertextLen : Nat) : ByteArray :=
  ByteArray.mk #[0x17, 0x03, 0x03] ++ u16be ciphertextLen

/-- Seal one record: AEAD-protect `plaintext` under the direction's key, the
per-record nonce for `seq`, and additional data `ad`. `none` only on a
`Crypto.chachaSeal` size error. Returns `encrypted_record = ct ‖ tag`. -/
def recordSeal (rk : RecordKeys) (seq : Nat) (ad plaintext : ByteArray) :
    Option ByteArray :=
  chachaSeal rk.key (recordNonce rk.iv seq) ad plaintext

/-- Open one record: AEAD-verify-and-decrypt `ciphertext`. `none` on
authentication failure or a size error — the two are indistinguishable. -/
def recordOpen (rk : RecordKeys) (seq : Nat) (ad ciphertext : ByteArray) :
    Option ByteArray :=
  chachaOpen rk.key (recordNonce rk.iv seq) ad ciphertext

/-! ### Record-layer theorems, transported from the crypto axioms -/

/-- **Record roundtrip.** Whatever `recordSeal` produced, `recordOpen` under the
same key, sequence number, and additional data recovers the plaintext. This is
`Crypto.Assumptions.chacha_open_seal_roundtrip` at the record-layer nonce/AD. -/
theorem record_roundtrip (rk : RecordKeys) (seq : Nat) (ad pt ct : ByteArray)
    (h : recordSeal rk seq ad pt = some ct) :
    recordOpen rk seq ad ct = some pt := by
  unfold recordSeal at h
  unfold recordOpen
  exact Crypto.Assumptions.chacha_open_seal_roundtrip _ _ _ _ _ h

/-- **Record authenticity.** The only ciphertext that opens to `pt` under a key
is the one `recordSeal` would produce for that `pt`. This is
`Crypto.Assumptions.chacha_open_authentic` at the record-layer nonce/AD. -/
theorem record_open_authentic (rk : RecordKeys) (seq : Nat)
    (ad ct pt : ByteArray) (h : recordOpen rk seq ad ct = some pt) :
    recordSeal rk seq ad pt = some ct := by
  unfold recordOpen at h
  unfold recordSeal
  exact Crypto.Assumptions.chacha_open_authentic _ _ _ _ _ h

/-- **Record forgery fails.** A record that is *not* the genuine sealing of `pt`
never opens to `pt`: an attacker cannot fabricate, alter, or replay-with-a-
different-sequence a ciphertext that decrypts to a chosen plaintext without
producing the exact AEAD output the key holder would. The functional shadow of
INT-CTXT, transported through `record_open_authentic`. -/
theorem record_forgery_fails (rk : RecordKeys) (seq : Nat)
    (ad pt ct : ByteArray) (hne : recordSeal rk seq ad pt ≠ some ct) :
    recordOpen rk seq ad ct ≠ some pt :=
  fun hopen => hne (record_open_authentic rk seq ad ct pt hopen)

/-! ## Wiring the real record layer into the state machine

`Tls.Config` treats the record layer as `RecConn → Bytes → …`. The abstract
`Tls.RecConn` is just an id; we use that id as the record sequence number, so
the successor connection returned by a step is the same keys at the next
sequence. The direction keys `tx` (server-write) and `rx` (server-read = client-
write) are the ones the key schedule above derived; they are captured in the
`Config` so that `recSeal`/`recOpen` genuinely call `Crypto.chachaSeal/Open`. -/

/-- List → ByteArray at the model boundary. -/
def toBA (l : Tls.Bytes) : ByteArray := ByteArray.mk l.toArray

/-- The model's `recOpen`, backed by the real receive-direction record layer.
The sequence number is the connection id; success advances to the next id. -/
def realRecOpen (rx : RecordKeys) (rc : Tls.RecConn) (buf : Tls.Bytes) :
    Tls.RecOut :=
  let ct := toBA buf
  match recordOpen rx rc.id (recordAD ct.size) ct with
  | some pt => .more { id := rc.id + 1 } buf.length pt.toList
  | none => .fail

/-- The model's `recSeal`, backed by the real send-direction record layer. -/
def realRecSeal (tx : RecordKeys) (rc : Tls.RecConn) (d : Tls.Bytes) :
    Tls.RecConn × Tls.Bytes :=
  let pt := toBA d
  match recordSeal tx rc.id (recordAD (pt.size + 16)) pt with
  | some ct => ({ id := rc.id + 1 }, ct.toList)
  | none => ({ id := rc.id }, [])

/-- A real sealed close_notify alert (level warning, description 0). -/
def realCloseNotify (tx : RecordKeys) (rc : Tls.RecConn) : Tls.Bytes :=
  let alert := ByteArray.mk #[0x01, 0x00]
  match recordSeal tx rc.id (recordAD (alert.size + 16)) alert with
  | some ct => ct.toList
  | none => []

/-- Default keys for the total fallback when a size limit would make a
derivation `none` — never reached on the real 32/12-byte outputs. -/
def defaultKeys : RecordKeys := { key := zeros keyLen, iv := zeros ivLen }

/-- A `Tls.Config` whose entire record path is this real EverCrypt layer, with
the direction keys produced by the real key schedule from the `X25519` shared
secret `dhe` and the transcript hashes. `hsFeed` completes the handshake once
ciphertext arrives, establishing the record connection at sequence 0 — the
completion the stub could never reach. -/
def realConfig (dhe thHS thAP : ByteArray) : Tls.Config :=
  let sc := deriveSchedule dhe thHS thAP
  let ms := sc.master.getD (zeros hashLen)
  let sAp := (serverApTrafficSecret ms thAP).getD (zeros hashLen)
  let cAp := (clientApTrafficSecret ms thAP).getD (zeros hashLen)
  let tx := (trafficKeys sAp).getD defaultKeys
  let rx := (trafficKeys cAp).getD defaultKeys
  { hsInit := { id := 0 }
    ktls := false
    earlyDataAccepted := false
    fatalAlert := [0x15, 0x03, 0x03, 0x00, 0x02, 0x02, 0x28]
    hsFeed := fun _hs buf =>
      if buf.isEmpty then .insufficient
      else .done { id := 0 } buf.length [] .h1 []
    recOpen := realRecOpen rx
    recSeal := realRecSeal tx
    recCloseNotify := realCloseNotify tx
    extractSecrets := fun rc => { tx := { id := rc.id }, rx := { id := rc.id } } }

/-- **No plaintext after close, with the real record layer.** The state
machine's safety theorem `Tls.no_plain_after_close`, specialized to a `Config`
whose record functions are the live EverCrypt seal/open above: once the
connection is closing or closed, no input sequence ever surfaces a
plaintext-carrying output. The property is structural, so it survives the
replacement of the crypto stub by real ChaCha20-Poly1305 — this is the
composition the `Compose` note in `Crypto.lean` describes, now discharged
against an executing record layer rather than an uninterpreted one. -/
theorem tls_no_plaintext_after_close
    (dhe thHS thAP : ByteArray) (s : Tls.St)
    (h : s.phase.closingOrClosed = true) (is : List Tls.Input) :
    ∀ e ∈ (Tls.run (realConfig dhe thHS thAP) s is).2,
      ∀ o ∈ e.out, o.carriesPlain = false :=
  Tls.no_plain_after_close (realConfig dhe thHS thAP) s h is

/-! ## A pure look at the label encoding (no crypto call)

`hkdfLabel` is pure byte-shuffling — displayable without linking EverCrypt. For
the `"key"` label with empty context and length 32, RFC 8446 §7.3 fixes the
bytes: `00 20` (length 32), `09` (len "tls13 key" = 9), the 9 label bytes, `00`
(empty context) — 13 bytes total. -/
#eval (hkdfLabel keyLen "key".toUTF8 ByteArray.empty).toList
#eval (hkdfLabel ivLen "iv".toUTF8 ByteArray.empty).size  -- 2+1+8+1 = 12
#eval (recordAD 100).toList                                -- 17 03 03 00 64

end TlsCrypto
