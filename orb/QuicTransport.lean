/-
# QuicTransport — the QUIC transport handshake + packet protection over verified crypto

The QUIC connection FSM (`Quic/Fsm.lean`) is a *sans-IO* deterministic machine:
packets enter it "already decrypted and parsed" (`Quic.Input.pktReceived`), so
the transport cryptography — the part that turns UDP bytes into those decrypted
packets — was stubbed. That is exactly why no off-the-shelf QUIC client can
handshake against the orb: there is no key schedule and no packet protection on
the wire, only a model that assumes the decryption already happened.

This module supplies the missing transport layer, computed over the SAME
EverCrypt primitives (`Crypto.lean`, HACL*/EverCrypt verified in F*) that the TLS
record layer already runs on, and mirroring `TlsCrypto.lean` step for step —
because RFC 9001 says QUIC *reuses* the TLS 1.3 key schedule. Three pieces:

* **Initial-secret derivation** (RFC 9001 §5.2). `initial_secret =
  HKDF-Extract(initial_salt, DCID)` over `Crypto.hkdfExtract`, then the client /
  server initial secrets via `HKDF-Expand-Label` — and QUIC's `HKDF-Expand-Label`
  is *bit-for-bit* the TLS one (same `"tls13 "` prefix), so we reuse
  `TlsCrypto.expandLabel` unchanged. The whole A.1 key block (secrets, key, iv,
  hp) is real HKDF output.

* **AEAD packet protection** (RFC 9001 §5.3). The per-packet nonce is the packet
  number XORed into the write-IV (identical construction to the TLS record nonce,
  so we reuse `TlsCrypto.recordNonce`); the additional data is the QUIC header;
  seal/open are `Crypto.chachaSeal` / `Crypto.chachaOpen`
  (TLS_CHACHA20_POLY1305_SHA256, a QUIC v1 cipher suite).

* **The handshake key transition** Initial → Handshake → 1-RTT (RFC 9001 §4, §7).
  A small monotone key-installation machine: the three encryption levels install
  in order and never uninstall, and 1-RTT keys are gated on the handshake keys
  already being present.

Theorems:

* `quic_initial_keys_real` — the initial secrets are a pure function of DCID
  (and the fixed salt) via real HKDF; equal DCID ⇒ equal secrets. Mirrors
  `TlsCrypto.keyschedule_deterministic`.
* `quic_packet_roundtrip` — seal then open a protected packet under the same
  key/pn/header recovers the plaintext. Transported from
  `Crypto.Assumptions.chacha_open_seal_roundtrip`.
* `quic_packet_forgery_fails` — a packet that is not the genuine sealing of `pt`
  never opens to `pt`. Transported from `Crypto.Assumptions.chacha_open_authentic`.
* `quic_no_1rtt_before_handshake` — with no handshake-key installation in the
  event stream, no 1-RTT packet is ever accepted (its open is never even
  reached). The key-schedule sibling of `Quic.no_appdata_before_established`.

The self-test (`QuicTransport.SelfTest.main`, run as an exe linking the crypto
shim) checks the derivations against the RFC 9001 Appendix A.1 test vectors on
live EverCrypt, plus a real ChaCha20-Poly1305 packet roundtrip.
-/

import Crypto
import TlsCrypto
import Quic.Fsm

namespace QuicTransport

open Crypto TlsCrypto

/-! ## Initial-secret derivation — RFC 9001 §5.2, over `Crypto` HKDF -/

/-- The QUIC v1 initial salt (RFC 9001 §5.2):
`0x38762cf7f55934b34d179ae6a4c80cadccbb7f0a`. -/
def initialSalt : ByteArray :=
  ByteArray.mk #[0x38, 0x76, 0x2c, 0xf7, 0xf5, 0x59, 0x34, 0xb3, 0x4d, 0x17,
                 0x9a, 0xe6, 0xa4, 0xc8, 0x0c, 0xad, 0xcc, 0xbb, 0x7f, 0x0a]

@[simp] theorem initialSalt_size : initialSalt.size = 20 := by
  simp [initialSalt, ByteArray.size]

/-- `initial_secret = HKDF-Extract(initial_salt, DCID)` (RFC 9001 §5.2), where the
Destination Connection ID of the client's first Initial packet is the IKM. -/
def initialSecret (dcid : ByteArray) : Option ByteArray :=
  hkdfExtract initialSalt dcid

/-- The SHA-256 secret length, in bytes (RFC 9001 §5.2 derives 32-byte secrets). -/
def secretLen : Nat := 32

/-- The record of the three cipher-independent initial secrets — the entire
RFC 9001 Appendix A.1 "secrets" column — as one value, so its determinism is a
single statement. -/
structure InitialSecrets where
  /-- `HKDF-Extract(initial_salt, DCID)`. -/
  initial : Option ByteArray
  /-- `HKDF-Expand-Label(initial_secret, "client in", "", 32)`. -/
  client : Option ByteArray
  /-- `HKDF-Expand-Label(initial_secret, "server in", "", 32)`. -/
  server : Option ByteArray

/-- Derive the client and server initial secrets from the DCID (RFC 9001 §5.2).
`expandLabel` is `TlsCrypto`'s `HKDF-Expand-Label` verbatim — RFC 9001 §5.1 fixes
QUIC's KDF to the TLS 1.3 one, `"tls13 "` prefix and all. -/
def initialSecrets (dcid : ByteArray) : InitialSecrets :=
  let is0 := initialSecret dcid
  { initial := is0
    client := is0.bind (fun s => expandLabel s "client in".toUTF8 ByteArray.empty secretLen)
    server := is0.bind (fun s => expandLabel s "server in".toUTF8 ByteArray.empty secretLen) }

/-! ## Packet-protection keys — RFC 9001 §5.1, over `Crypto` HKDF -/

/-- The QUIC AEAD nonce / write-IV length (RFC 9001 §5.1): 12 bytes. -/
def ivLen : Nat := 12

/-- The ChaCha20-Poly1305 packet-protection key length. -/
def chachaKeyLen : Nat := 32

/-- The ChaCha20 header-protection key length (RFC 9001 §5.4.4). -/
def chachaHpLen : Nat := 32

/-- One encryption level's packet-protection material (RFC 9001 §5.1): the AEAD
`key`, the write-`iv`, and the header-protection key `hp`. -/
structure PacketKeys where
  key : ByteArray
  iv : ByteArray
  hp : ByteArray

/-- Derive one level's packet keys from its traffic secret (RFC 9001 §5.1):
`key = HKDF-Expand-Label(secret, "quic key", "", keyLen)`,
`iv  = HKDF-Expand-Label(secret, "quic iv", "", 12)`,
`hp  = HKDF-Expand-Label(secret, "quic hp", "", hpLen)`. `keyLen`/`hpLen` vary by
cipher (16 for AES-128-GCM, 32 for ChaCha20-Poly1305); `iv` is always 12. -/
def derivePacketKeys (secret : ByteArray) (keyLen hpLen : Nat) : Option PacketKeys :=
  match expandLabel secret "quic key".toUTF8 ByteArray.empty keyLen,
        expandLabel secret "quic iv".toUTF8 ByteArray.empty ivLen,
        expandLabel secret "quic hp".toUTF8 ByteArray.empty hpLen with
  | some k, some iv, some hp => some { key := k, iv := iv, hp := hp }
  | _, _, _ => none

/-- The ChaCha20-Poly1305 packet keys (32-byte AEAD key, 32-byte HP key). This is
the cipher the AEAD packet protection below runs on. -/
def deriveChachaKeys (secret : ByteArray) : Option PacketKeys :=
  derivePacketKeys secret chachaKeyLen chachaHpLen

/-- The AES-128-GCM packet-protection key length (RFC 9001 §5.2). -/
def aesKeyLen : Nat := 16

/-- The AES header-protection key length (RFC 9001 §5.4.3): a 16-byte AES key. -/
def aesHpLen : Nat := 16

/-- The **AES-128-GCM** packet keys (16-byte AEAD key, 16-byte HP key) — the cipher
RFC 9001 §5.2 MANDATES for QUIC Initial packets, hence the one every off-the-shelf
client's Initial arrives under. Same HKDF-Expand-Label derivation as the ChaCha
keys, at the AES lengths. -/
def deriveAesKeys (secret : ByteArray) : Option PacketKeys :=
  derivePacketKeys secret aesKeyLen aesHpLen

/-! ## AEAD packet protection — RFC 9001 §5.3, over `Crypto` ChaCha20-Poly1305 -/

/-- The AEAD nonce for packet number `pn` (RFC 9001 §5.3): the packet number,
big-endian, left-padded with zeros to the IV length, XORed with the write-IV.
This is exactly `TlsCrypto.recordNonce`'s construction (RFC 8446 §5.3), reused. -/
def packetNonce (iv : ByteArray) (pn : Nat) : ByteArray := recordNonce iv pn

/-- Seal one packet's payload (RFC 9001 §5.3): AEAD-protect `payload` under the
level's key, the per-packet nonce for `pn`, and additional data `header` (the
unprotected QUIC header). `none` only on a `Crypto.chachaSeal` size error.
Returns the protected payload `ct ‖ tag`. -/
def sealPacket (pk : PacketKeys) (pn : Nat) (header payload : ByteArray) :
    Option ByteArray :=
  chachaSeal pk.key (packetNonce pk.iv pn) header payload

/-- Open one packet's protected payload (RFC 9001 §5.3): AEAD-verify-and-decrypt.
`none` on authentication failure or a size error — indistinguishable. -/
def openPacket (pk : PacketKeys) (pn : Nat) (header ciphertext : ByteArray) :
    Option ByteArray :=
  chachaOpen pk.key (packetNonce pk.iv pn) header ciphertext

/-- Seal one packet's payload under **AES-128-GCM** (RFC 9001 §5.3) — the cipher a
real client's Initial uses. Identical nonce/AAD construction to the ChaCha path;
the AEAD is `Crypto.aesGcmSeal` (verified EverCrypt/Vale on x86, portable aws-lc-rs
fallback off-x86 — see the trust ledger). `none` only on a size error. -/
def sealPacketAes (pk : PacketKeys) (pn : Nat) (header payload : ByteArray) :
    Option ByteArray :=
  aesGcmSeal pk.key (packetNonce pk.iv pn) header payload

/-- Open one packet's protected payload under **AES-128-GCM** (RFC 9001 §5.3):
AEAD-verify-and-decrypt via `Crypto.aesGcmOpen`. `none` on authentication failure
or a size error — indistinguishable. This is the AEAD half of decrypting a real
off-the-shelf client's Initial packet. -/
def openPacketAes (pk : PacketKeys) (pn : Nat) (header ciphertext : ByteArray) :
    Option ByteArray :=
  aesGcmOpen pk.key (packetNonce pk.iv pn) header ciphertext

/-! ## The handshake key transition — Initial → Handshake → 1-RTT

QUIC installs three encryption levels in strict order as the TLS handshake
progresses (RFC 9001 §4, §7): Initial keys (from the DCID above), then Handshake
keys (from the TLS handshake-traffic secrets), then 1-RTT / application keys
(from the TLS application-traffic secrets). Keys, once installed, are never
removed, and a level is never installed out of order. The machine below is that
monotone discipline; the single property that matters here is that 1-RTT keys
are gated on the Handshake keys already being present. -/

/-- The installed key material of a connection: Initial always present; Handshake
and 1-RTT populated as the handshake advances. -/
structure KeyState where
  initial : PacketKeys
  handshake : Option PacketKeys
  oneRtt : Option PacketKeys

/-- Fresh key state: only the Initial keys, derived from the DCID. -/
def KeyState.start (ik : PacketKeys) : KeyState :=
  { initial := ik, handshake := none, oneRtt := none }

/-- The events that install the next encryption level, each carrying the TLS
traffic secret the level's keys are derived from. -/
inductive KeyEvent where
  /-- The TLS handshake-traffic secret is available: install Handshake keys. -/
  | installHandshake (secret : ByteArray)
  /-- The TLS application-traffic secret is available: install 1-RTT keys. -/
  | installOneRtt (secret : ByteArray)

/-- Is this the handshake-key install event? -/
def KeyEvent.isInstallHandshake : KeyEvent → Bool
  | .installHandshake _ => true
  | .installOneRtt _ => false

/-- Install the next level. Monotone: Handshake installs only if not already
installed; 1-RTT installs only once Handshake keys exist and 1-RTT does not yet
(RFC 9001's strict level ordering). A crypto size failure leaves the level
uninstalled — which cannot break the ordering invariant, since 1-RTT is gated on
Handshake being present, not on it being derivable. -/
def KeyState.step (ks : KeyState) : KeyEvent → KeyState
  | .installHandshake s =>
      match ks.handshake with
      | some _ => ks
      | none => { ks with handshake := deriveChachaKeys s }
  | .installOneRtt s =>
      match ks.handshake, ks.oneRtt with
      | some _, none => { ks with oneRtt := deriveChachaKeys s }
      | _, _ => ks

/-- Run a stream of install events. -/
def KeyState.run (ks : KeyState) : List KeyEvent → KeyState
  | [] => ks
  | e :: es => (ks.step e).run es

/-- Accept a 1-RTT (application) packet: only reachable when 1-RTT keys are
installed, and then only if AEAD open succeeds. -/
def KeyState.acceptOneRtt (ks : KeyState) (pn : Nat) (header ct : ByteArray) :
    Option ByteArray :=
  match ks.oneRtt with
  | some pk => openPacket pk pn header ct
  | none => none

/-- Level-ordering invariant: 1-RTT keys are installed only if Handshake keys
are. Every reachable state satisfies it (`run_wf`). -/
def KeyState.Wf (ks : KeyState) : Prop :=
  ks.oneRtt.isSome = true → ks.handshake.isSome = true

/-! ## Theorems -/

/-! ### `quic_initial_keys_real` — the initial secrets are a pure HKDF function -/

/-- The initial secret is exactly `HKDF-Extract(initial_salt, DCID)` — no hidden
input. (`rfl`-checkable spec conformance, RFC 9001 §5.2.) -/
theorem initialSecrets_initial (dcid : ByteArray) :
    (initialSecrets dcid).initial = hkdfExtract initialSalt dcid := rfl

/-- The client initial secret is exactly
`HKDF-Expand-Label(initial_secret, "client in", "", 32)`. -/
theorem initialSecrets_client (dcid : ByteArray) :
    (initialSecrets dcid).client
      = (hkdfExtract initialSalt dcid).bind
          (fun s => expandLabel s "client in".toUTF8 ByteArray.empty secretLen) := rfl

/-- The server initial secret is exactly
`HKDF-Expand-Label(initial_secret, "server in", "", 32)`. -/
theorem initialSecrets_server (dcid : ByteArray) :
    (initialSecrets dcid).server
      = (hkdfExtract initialSalt dcid).bind
          (fun s => expandLabel s "server in".toUTF8 ByteArray.empty secretLen) := rfl

/-- **The initial keys are a pure function of the DCID (and the fixed salt) via
real HKDF.** There is no randomness and no hidden state: the derivation is a
composition of the pure `Crypto` primitives `hkdfExtract` and `hkdfExpand` over
the constant `initialSalt`, so equal DCIDs yield equal secrets. This is the QUIC
sibling of `TlsCrypto.keyschedule_deterministic`. -/
theorem quic_initial_keys_real {dcid dcid' : ByteArray} (h : dcid = dcid') :
    initialSecrets dcid = initialSecrets dcid' := by
  subst h; rfl

/-! ### `quic_packet_roundtrip` — AEAD seal/open recovers the payload -/

/-- **Packet roundtrip.** Whatever `sealPacket` produced, `openPacket` under the
same key, packet number, and header (additional data) recovers the payload. This
is `Crypto.Assumptions.chacha_open_seal_roundtrip` at the QUIC packet nonce/AAD —
the same discharge `TlsCrypto.record_roundtrip` makes at the TLS record layer. -/
theorem quic_packet_roundtrip (pk : PacketKeys) (pn : Nat)
    (header pt ct : ByteArray) (h : sealPacket pk pn header pt = some ct) :
    openPacket pk pn header ct = some pt := by
  unfold sealPacket at h
  unfold openPacket
  exact Crypto.Assumptions.chacha_open_seal_roundtrip _ _ _ _ _ h

/-- **Packet authenticity.** The only protected payload that opens to `pt` under
a key is the one `sealPacket` would produce for that `pt`. This is
`Crypto.Assumptions.chacha_open_authentic` at the QUIC packet nonce/AAD. -/
theorem quic_packet_open_authentic (pk : PacketKeys) (pn : Nat)
    (header ct pt : ByteArray) (h : openPacket pk pn header ct = some pt) :
    sealPacket pk pn header pt = some ct := by
  unfold openPacket at h
  unfold sealPacket
  exact Crypto.Assumptions.chacha_open_authentic _ _ _ _ _ h

/-- **Packet forgery fails.** A protected payload that is not the genuine sealing
of `pt` never opens to `pt`: an attacker cannot fabricate, alter, or replay-under-
a-different-packet-number a ciphertext that decrypts to a chosen payload without
producing the exact AEAD output the key holder would. The functional shadow of
INT-CTXT, transported through `quic_packet_open_authentic`. -/
theorem quic_packet_forgery_fails (pk : PacketKeys) (pn : Nat)
    (header pt ct : ByteArray) (hne : sealPacket pk pn header pt ≠ some ct) :
    openPacket pk pn header ct ≠ some pt :=
  fun ho => hne (quic_packet_open_authentic pk pn header ct pt ho)

/-- **AES packet roundtrip.** The AES-128-GCM sibling of `quic_packet_roundtrip`:
whatever `sealPacketAes` produced, `openPacketAes` under the same key/pn/header
recovers the payload. Discharged by `Crypto.Assumptions.aesgcm_open_seal_roundtrip`
at the QUIC packet nonce/AAD — so the AES Initial path is roundtrip-correct exactly
as the ChaCha path is. -/
theorem quic_aes_packet_roundtrip (pk : PacketKeys) (pn : Nat)
    (header pt ct : ByteArray) (h : sealPacketAes pk pn header pt = some ct) :
    openPacketAes pk pn header ct = some pt := by
  unfold sealPacketAes at h
  unfold openPacketAes
  exact Crypto.Assumptions.aesgcm_open_seal_roundtrip _ _ _ _ _ h

/-- **AES packet authenticity.** The only protected payload that opens to `pt`
under a key is the one `sealPacketAes` would produce for that `pt`.
`Crypto.Assumptions.aesgcm_open_authentic` at the QUIC packet nonce/AAD. -/
theorem quic_aes_packet_open_authentic (pk : PacketKeys) (pn : Nat)
    (header ct pt : ByteArray) (h : openPacketAes pk pn header ct = some pt) :
    sealPacketAes pk pn header pt = some ct := by
  unfold openPacketAes at h
  unfold sealPacketAes
  exact Crypto.Assumptions.aesgcm_open_authentic _ _ _ _ _ h

/-- **AES packet forgery fails.** A protected payload that is not the genuine AES
sealing of `pt` never opens to `pt` — the functional shadow of INT-CTXT for the
AES-128-GCM Initial cipher, transported through `quic_aes_packet_open_authentic`. -/
theorem quic_aes_packet_forgery_fails (pk : PacketKeys) (pn : Nat)
    (header pt ct : ByteArray) (hne : sealPacketAes pk pn header pt ≠ some ct) :
    openPacketAes pk pn header ct ≠ some pt :=
  fun ho => hne (quic_aes_packet_open_authentic pk pn header ct pt ho)

/-! ### `quic_no_1rtt_before_handshake` — the level-ordering gate -/

/-- The fresh key state is well-formed (no 1-RTT keys installed). -/
theorem KeyState.start_wf (ik : PacketKeys) : (KeyState.start ik).Wf := by
  intro h; simp [KeyState.start] at h

/-- One install step preserves the level-ordering invariant. -/
theorem KeyState.step_wf {ks : KeyState} (h : ks.Wf) (e : KeyEvent) :
    (ks.step e).Wf := by
  cases e with
  | installHandshake s =>
      unfold KeyState.step
      cases hh : ks.handshake with
      | some pk => simpa [hh] using h
      | none =>
          -- handshake becomes (maybe) some; oneRtt was none by `h` since
          -- handshake was none, so the invariant holds vacuously afterwards.
          intro hone
          have hno : ks.oneRtt.isSome = true → False := by
            intro ho; have := h ho; rw [hh] at this; simp at this
          simp only [hh]
          -- new oneRtt = ks.oneRtt; it is not some, so `hone` is impossible
          exact absurd hone (by
            intro ho; exact hno ho)
  | installOneRtt s =>
      unfold KeyState.step
      cases hh : ks.handshake with
      | none => simpa [hh] using h
      | some pkh =>
          cases ho : ks.oneRtt with
          | some pko => simpa [hh, ho] using h
          | none =>
              -- installs oneRtt := deriveChachaKeys s; handshake is some
              intro _; simp [hh, ho]
end QuicTransport

/-! re-open to keep the file linear -/
namespace QuicTransport
open Crypto TlsCrypto

/-- Every reachable key state satisfies the level-ordering invariant. -/
theorem KeyState.run_wf {ks : KeyState} (h : ks.Wf) (es : List KeyEvent) :
    (ks.run es).Wf := by
  induction es generalizing ks with
  | nil => exact h
  | cons e es ih => exact ih (KeyState.step_wf h e)

/-- **1-RTT acceptance requires installed handshake keys.** In any well-formed
state, if a 1-RTT packet opens successfully then the handshake keys are present.
The invariant makes this immediate; `run_wf` supplies it for every reachable
state. -/
theorem quic_1rtt_requires_handshake {ks : KeyState} (h : ks.Wf)
    {pn : Nat} {header ct pt : ByteArray}
    (hacc : ks.acceptOneRtt pn header ct = some pt) :
    ks.handshake.isSome = true := by
  unfold KeyState.acceptOneRtt at hacc
  cases ho : ks.oneRtt with
  | none => rw [ho] at hacc; simp at hacc
  | some pk => exact h (by rw [ho]; rfl)

/-- If no handshake-key install occurs, both the Handshake and 1-RTT levels stay
uninstalled: 1-RTT install is gated on Handshake being present, so it can never
fire. -/
theorem KeyState.run_none_of_none {ks : KeyState}
    (hks : ks.handshake = none ∧ ks.oneRtt = none)
    (es : List KeyEvent) (h : ∀ e ∈ es, e.isInstallHandshake = false) :
    (ks.run es).handshake = none ∧ (ks.run es).oneRtt = none := by
  induction es generalizing ks with
  | nil => exact hks
  | cons e es ih =>
      apply ih
      · obtain ⟨hh, ho⟩ := hks
        cases e with
        | installHandshake s =>
            have : (KeyEvent.installHandshake s).isInstallHandshake = false :=
              h _ (List.mem_cons_self _ _)
            simp [KeyEvent.isInstallHandshake] at this
        | installOneRtt s =>
            -- handshake = none ⇒ step is a no-op
            have hstep : ks.step (KeyEvent.installOneRtt s) = ks := by
              unfold KeyState.step; rw [hh]
            rw [hstep]; exact ⟨hh, ho⟩
      · intro e' he'; exact h e' (List.mem_cons_of_mem _ he')

/-- **No 1-RTT packet is accepted before the handshake keys are installed.** If
the event stream contains no handshake-key install, then no 1-RTT packet is ever
accepted — the acceptance function returns `none` for every packet, because the
1-RTT keys were never installed (the ordering gate held). This is the
key-schedule sibling of `Quic.no_appdata_before_established`: that FSM theorem
gates application-data *delivery* on the established phase; this one gates the
*existence of the keys that could open a 1-RTT packet at all* on the handshake. -/
theorem quic_no_1rtt_before_handshake (ik : PacketKeys) (es : List KeyEvent)
    (h : ∀ e ∈ es, e.isInstallHandshake = false)
    (pn : Nat) (header ct : ByteArray) :
    ((KeyState.start ik).run es).acceptOneRtt pn header ct = none := by
  have hnone := KeyState.run_none_of_none (ks := KeyState.start ik)
    ⟨rfl, rfl⟩ es h
  unfold KeyState.acceptOneRtt
  rw [hnone.2]

end QuicTransport

/-! ## Self-test against the RFC 9001 Appendix A.1 vectors

Run as an executable linking `ffi/crypto_shim.o` + `libevercrypt.a` (the same
recipe as `tls-keyschedule-selftest`). It derives the A.1 initial keys on live
EverCrypt and checks every hex value; then runs a real ChaCha20-Poly1305 packet
roundtrip through `sealPacket`/`openPacket`. -/

namespace QuicTransport.SelfTest

open Crypto TlsCrypto QuicTransport

/-- Parse a hex string (spaces ignored) into a `ByteArray`. -/
def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.filter (· ≠ ' ')
  let hexVal : Char → Option UInt8 := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
    else none
  let rec go : List Char → ByteArray → ByteArray
    | hi :: lo :: rest, acc =>
      match hexVal hi, hexVal lo with
      | some h, some l => go rest (acc.push (h * 16 + l))
      | _, _ => acc
    | _, acc => acc
  go cs (ByteArray.mk #[])

def eqBA (a b : ByteArray) : Bool := a.toList == b.toList

def optEq (a : Option ByteArray) (b : ByteArray) : Bool :=
  match a with
  | some x => eqBA x b
  | none => false

structure Check where
  name : String
  ok : Bool

def checks : List Check := Id.run do
  let mut cs : List Check := []

  -- RFC 9001 A.1: the client-chosen 8-byte Destination Connection ID.
  let dcid := ofHex "8394c8f03e515708"

  -- The HkdfLabel encodings are pure byte-shuffling (no crypto) — check them
  -- against the exact bytes RFC 9001 A.1 prints.
  cs := cs ++ [⟨"A.1 HkdfLabel \"client in\"",
    eqBA (hkdfLabel secretLen "client in".toUTF8 ByteArray.empty)
      (ofHex "00200f746c73313320636c69656e7420696e00")⟩]
  cs := cs ++ [⟨"A.1 HkdfLabel \"quic key\"",
    eqBA (hkdfLabel 16 "quic key".toUTF8 ByteArray.empty)
      (ofHex "00100e746c7331332071756963206b657900")⟩]
  cs := cs ++ [⟨"A.1 HkdfLabel \"quic iv\"",
    eqBA (hkdfLabel ivLen "quic iv".toUTF8 ByteArray.empty)
      (ofHex "000c0d746c733133207175696320697600")⟩]
  cs := cs ++ [⟨"A.1 HkdfLabel \"quic hp\"",
    eqBA (hkdfLabel 16 "quic hp".toUTF8 ByteArray.empty)
      (ofHex "00100d746c733133207175696320687000")⟩]

  -- The initial secret and the client/server secrets — live HKDF over EverCrypt.
  let secs := initialSecrets dcid
  cs := cs ++ [⟨"A.1 initial_secret", optEq secs.initial
    (ofHex "7db5df06e7a69e432496adedb00851923595221596ae2ae9fb8115c1e9ed0a44")⟩]
  cs := cs ++ [⟨"A.1 client_initial_secret", optEq secs.client
    (ofHex "c00cf151ca5be075ed0ebfb5c80323c42d6b7db67881289af4008f1f6c357aea")⟩]
  cs := cs ++ [⟨"A.1 server_initial_secret", optEq secs.server
    (ofHex "3c199828fd139efd216c155ad844cc81fb82fa8d7446fa7d78be803acdda951b")⟩]

  -- The client packet keys at the AES-128-GCM lengths RFC 9001 A.1 uses
  -- (key 16, iv 12, hp 16). The derivation is cipher-independent HKDF output.
  match secs.client with
  | some cs0 =>
      match derivePacketKeys cs0 16 16 with
      | some pk =>
          cs := cs ++ [⟨"A.1 client key",
            eqBA pk.key (ofHex "1f369613dd76d5467730efcbe3b1a22d")⟩]
          cs := cs ++ [⟨"A.1 client iv",
            eqBA pk.iv (ofHex "fa044b2f42a3fd3b46fb255c")⟩]
          cs := cs ++ [⟨"A.1 client hp",
            eqBA pk.hp (ofHex "9f50449e04a0e810283a1e9933adedd2")⟩]
      | none => cs := cs ++ [⟨"A.1 client packet keys derived", false⟩]
  | none => cs := cs ++ [⟨"client_initial_secret present", false⟩]

  -- The server packet keys (key 16, iv 12, hp 16).
  match secs.server with
  | some ss0 =>
      match derivePacketKeys ss0 16 16 with
      | some pk =>
          cs := cs ++ [⟨"A.1 server key",
            eqBA pk.key (ofHex "cf3a5331653c364c88f0f379b6067e37")⟩]
          cs := cs ++ [⟨"A.1 server iv",
            eqBA pk.iv (ofHex "0ac1493ca1905853b0bba03e")⟩]
          cs := cs ++ [⟨"A.1 server hp",
            eqBA pk.hp (ofHex "c206b8d9b9f0f37644430b490eeaa314")⟩]
      | none => cs := cs ++ [⟨"A.1 server packet keys derived", false⟩]
  | none => cs := cs ++ [⟨"server_initial_secret present", false⟩]

  -- A real ChaCha20-Poly1305 packet roundtrip: derive 32-byte ChaCha keys from
  -- the client initial secret, seal a payload under a header at packet number 2,
  -- open it back; then check that tamper and wrong-pn both fail.
  match secs.client with
  | some cs0 =>
      match deriveChachaKeys cs0 with
      | some pk =>
          let header := ofHex "c300000001088394c8f03e5157080000449e00000002"
          let payload := "quic 1-rtt-style payload over real chacha20-poly1305".toUTF8
          match sealPacket pk 2 header payload with
          | some ct =>
              cs := cs ++ [⟨"ChaCha packet seal→open roundtrip (pn 2)",
                optEq (openPacket pk 2 header ct) payload⟩]
              cs := cs ++ [⟨"open at wrong packet number → none",
                (openPacket pk 3 header ct).isNone⟩]
              let bad := ByteArray.mk (ct.toList.set 0 (ct.toList.headD 0 ^^^ 0xff)).toArray
              cs := cs ++ [⟨"tampered payload → none",
                (openPacket pk 2 header bad).isNone⟩]
              let badHdr := ByteArray.mk (header.toList.set 0 (header.toList.headD 0 ^^^ 0x01)).toArray
              cs := cs ++ [⟨"altered header (AAD) → none",
                (openPacket pk 2 badHdr ct).isNone⟩]
          | none => cs := cs ++ [⟨"ChaCha packet seal produced none", false⟩]
      | none => cs := cs ++ [⟨"ChaCha packet keys derived", false⟩]
  | none => cs := cs ++ [⟨"client secret for chacha keys", false⟩]

  -- A real AES-128-GCM packet roundtrip: derive the 16-byte AES Initial keys from
  -- the client initial secret (the cipher RFC 9001 §5.2 mandates for Initials),
  -- seal a payload under a header at packet number 2, open it back; then check
  -- tamper and wrong-pn both fail — the AES sibling of the ChaCha roundtrip above.
  match secs.client with
  | some cs0 =>
      match deriveAesKeys cs0 with
      | some pk =>
          let header := ofHex "c300000001088394c8f03e5157080000449e00000002"
          let payload := "quic aes-128-gcm initial payload over real aes-gcm".toUTF8
          match sealPacketAes pk 2 header payload with
          | some ct =>
              cs := cs ++ [⟨"AES-128-GCM packet seal→open roundtrip (pn 2)",
                optEq (openPacketAes pk 2 header ct) payload⟩]
              cs := cs ++ [⟨"AES open at wrong packet number → none",
                (openPacketAes pk 3 header ct).isNone⟩]
              let bad := ByteArray.mk (ct.toList.set 0 (ct.toList.headD 0 ^^^ 0xff)).toArray
              cs := cs ++ [⟨"AES tampered payload → none",
                (openPacketAes pk 2 header bad).isNone⟩]
              let badHdr := ByteArray.mk (header.toList.set 0 (header.toList.headD 0 ^^^ 0x01)).toArray
              cs := cs ++ [⟨"AES altered header (AAD) → none",
                (openPacketAes pk 2 badHdr ct).isNone⟩]
          | none => cs := cs ++ [⟨"AES packet seal produced none", false⟩]
      | none => cs := cs ++ [⟨"AES packet keys derived", false⟩]
  | none => cs := cs ++ [⟨"client secret for aes keys", false⟩]

  return cs

def main : IO UInt32 := do
  let cs := checks
  for c in cs do
    IO.println s!"[{if c.ok then "PASS" else "FAIL"}] {c.name}"
  let failed := cs.filter (!·.ok)
  if failed.isEmpty then
    IO.println s!"\nall {cs.length} QUIC transport vectors passed (RFC 9001 A.1 + ChaCha roundtrip)"
    return 0
  else
    IO.eprintln s!"\n{failed.length} of {cs.length} FAILED"
    return 1

end QuicTransport.SelfTest

def main : IO UInt32 := QuicTransport.SelfTest.main
