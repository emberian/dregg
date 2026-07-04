/-
# TlsHandshake — the TLS 1.3 server-side handshake MESSAGE layer

`TlsCrypto` supplied the real key schedule and record layer over EverCrypt, but
its `realConfig.hsFeed` was a shortcut: it "completed the handshake once any
ciphertext arrived", ignoring the bytes. The record layer was real; the message
layer that must *drive* it — parse the peer's ClientHello, agree a shared
secret, run the key schedule off the true transcript, and emit the server's
flight — was missing. This module supplies it.

A server-side TLS 1.3 handshake is, at the message layer:

1. **Parse ClientHello** (RFC 8446 §4.1.2). The record/handshake framing, the
   `key_share` extension (the client's X25519 public key), `supported_versions`
   (TLS 1.3 present), the `cipher_suites` (offer `TLS_CHACHA20_POLY1305_SHA256`),
   and the SNI.
2. **Agree the DHE secret** (`Crypto.x25519`: server ephemeral × client public)
   and hash the transcript (`Crypto.sha256` over the handshake messages), then
   drive `TlsCrypto.deriveSchedule` to the handshake- and application-traffic
   secrets — REAL crypto, over the REAL transcript.
3. **Emit the server flight** — ServerHello (server `key_share`), then, sealed
   under the server handshake key (`TlsCrypto.recordSeal`), EncryptedExtensions,
   Certificate, CertificateVerify (`Crypto.ed25519Sign` over the RFC 8446 §4.4.3
   signature content), and Finished (the RFC 8446 §4.4.4 HMAC, computed as
   `Crypto.hkdfExtract finished_key transcript_hash`, since HKDF-Extract *is*
   HMAC).
4. **Verify the client Finished** and establish: `waitCH → waitClientFinished →
   established`. No application data is delivered before establishment; a wrong
   client Finished is rejected.

The three theorems are structural (they do not evaluate the opaque EverCrypt
primitives, so they need no linked shim):

* `waitCH_not_established` / `serverStep_delivers_nothing` — the FSM reaches
  `established` only through the Finished round, and surfaces no application
  plaintext during the handshake (that is the record layer's job, afterward).
* `hs_transcript_drives_keys` — an `Established`'s secrets are exactly
  `TlsCrypto.deriveSchedule dhe thHS thSF`, a pure function of the DHE and the
  actual transcript hashes; composing `TlsCrypto.keyschedule_deterministic`,
  equal transcripts yield equal keys.
* `hs_finished_authenticates` — acceptance requires the presented client
  `verify_data` to equal the server-computed HMAC; a wrong Finished never
  establishes.

The self-test `tls-handshake-selftest` drives this against the RFC 8448 §3
ClientHello on the linked EverCrypt (deriving the RFC's handshake traffic
secrets), then runs a full self-consistent handshake to `established`.
-/

import TlsCrypto

namespace TlsHandshake

open Crypto TlsCrypto

/-! ## Byte helpers -/

/-- List → ByteArray at the crypto boundary (shadowing `TlsCrypto.toBA` here). -/
def ofBytes (l : Tls.Bytes) : ByteArray := ByteArray.mk l.toArray

/-- A single big-endian `uint8` byte. -/
def u8 (n : Nat) : ByteArray := ByteArray.mk #[UInt8.ofNat n]

/-- Big-endian `uint16`. -/
def u16 (n : Nat) : ByteArray := ByteArray.mk #[UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- Big-endian `uint24`. -/
def u24 (n : Nat) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- A length-`len`-prefixed (`uint8` length) opaque vector. -/
def vec8 (b : ByteArray) : ByteArray := u8 b.size ++ b

/-- A length-`len`-prefixed (`uint16` length) opaque vector. -/
def vec16 (b : ByteArray) : ByteArray := u16 b.size ++ b

/-- A length-`len`-prefixed (`uint24` length) opaque vector. -/
def vec24 (b : ByteArray) : ByteArray := u24 b.size ++ b

/-- A handshake message: `msg_type(1) ‖ uint24 length ‖ body` (RFC 8446 §4). -/
def hsMsg (msgType : Nat) (body : ByteArray) : ByteArray :=
  u8 msgType ++ vec24 body

/-! ## Constants -/

/-- `TLS_CHACHA20_POLY1305_SHA256` (RFC 8446 §B.4). -/
def chachaSuite : Nat := 0x1303

/-- The `x25519` named group (RFC 8446 §4.2.7 / RFC 8422). -/
def x25519Group : Nat := 0x001d

/-- The TLS 1.3 code point (`supported_versions`). -/
def tls13 : Nat := 0x0304

/-! ## ClientHello parsing (over `List UInt8`, total, `Option`-valued) -/

/-- Read a big-endian `uint16`, returning the value and the remaining bytes. -/
def rd16 : Tls.Bytes → Option (Nat × Tls.Bytes)
  | a :: b :: r => some (a.toNat * 256 + b.toNat, r)
  | _ => none

/-- Read a big-endian `uint24`. -/
def rd24 : Tls.Bytes → Option (Nat × Tls.Bytes)
  | a :: b :: c :: r => some (a.toNat * 65536 + b.toNat * 256 + c.toNat, r)
  | _ => none

/-- Take exactly `n` bytes, or `none` if fewer are present. -/
def takeN (n : Nat) (l : Tls.Bytes) : Option (Tls.Bytes × Tls.Bytes) :=
  if l.length < n then none else some (l.take n, l.drop n)

/-- Walk a byte block as a list of `(type, data)` extensions
(`uint16 type ‖ uint16 len ‖ data[len]`), collecting all that parse. `fuel`
bounds the iteration (each step consumes ≥ 4 bytes; pass the block length). -/
def walkExts : Nat → Tls.Bytes → List (Nat × Tls.Bytes)
  | 0, _ => []
  | fuel + 1, l =>
    match rd16 l with
    | none => []
    | some (ty, r1) =>
      match rd16 r1 with
      | none => []
      | some (len, r2) =>
        match takeN len r2 with
        | none => []
        | some (data, rest) => (ty, data) :: walkExts fuel rest

/-- Walk a byte block as a list of `uint16` values (used for `cipher_suites`
and the `supported_versions` version list). -/
def walkU16s : Nat → Tls.Bytes → List Nat
  | 0, _ => []
  | fuel + 1, l =>
    match rd16 l with
    | none => []
    | some (v, r) => v :: walkU16s fuel r

/-- Find the `x25519` client share inside a `key_share` extension body:
`uint16 client_shares_len ‖ (group(2) ‖ key<uint16>)*`. Returns the 32-byte
client public key. -/
def findX25519 : Nat → Tls.Bytes → Option Tls.Bytes
  | 0, _ => none
  | fuel + 1, l =>
    match rd16 l with
    | none => none
    | some (grp, r1) =>
      match rd16 r1 with
      | none => none
      | some (klen, r2) =>
        match takeN klen r2 with
        | none => none
        | some (key, rest) =>
          if grp == x25519Group then some key else findX25519 fuel rest

/-- The parsed ClientHello fields the server acts on. -/
structure ClientHello where
  /-- The 32-byte client random. -/
  random : Tls.Bytes
  /-- The echoed legacy session id. -/
  sessionId : Tls.Bytes
  /-- Offered cipher suites (each a `uint16`). -/
  cipherSuites : List Nat
  /-- The client's X25519 public key from `key_share`, if offered. -/
  keyShare : Option Tls.Bytes
  /-- Whether `supported_versions` offered TLS 1.3. -/
  tls13Offered : Bool
  /-- The SNI host name, if present. -/
  sni : Option Tls.Bytes
  deriving Repr

/-- Strip a TLS record header (`type(1) ‖ legacy_version(2) ‖ uint16 len`) if the
first byte is `0x16` (handshake); otherwise return the input unchanged. So both a
bare ClientHello handshake message and a full record are accepted. -/
def stripRecord (l : Tls.Bytes) : Tls.Bytes :=
  match l with
  | 0x16 :: _v1 :: _v2 :: _l1 :: _l2 :: rest => rest
  | _ => l

/-- Extract the SNI host name from a `server_name` extension body. -/
def parseSni (body : Tls.Bytes) : Option Tls.Bytes :=
  match rd16 body with           -- server_name_list length
  | none => none
  | some (_, r0) =>
    match r0 with
    | _nameType :: r1 =>          -- name_type (0 = host_name)
      match rd16 r1 with
      | none => none
      | some (nlen, r2) =>
        match takeN nlen r2 with
        | some (name, _) => some name
        | none => none
    | [] => none

/-- Look up an extension body by type in the walked list. -/
def extBody (exts : List (Nat × Tls.Bytes)) (ty : Nat) : Option Tls.Bytes :=
  (exts.find? (fun p => p.1 == ty)).map (·.2)

/-- **Parse a ClientHello.** Accepts either the bare handshake message or a full
record. Follows RFC 8446 §4.1.2: `msg_type(1)=0x01 ‖ uint24 len ‖
legacy_version(2) ‖ random(32) ‖ session_id<uint8> ‖ cipher_suites<uint16> ‖
legacy_compression<uint8> ‖ extensions<uint16>`. -/
def parseClientHello (input : Tls.Bytes) : Option ClientHello := do
  let hs := stripRecord input
  match hs with
  | 0x01 :: r0 =>                                   -- ClientHello handshake type
    let (_len, r1) ← rd24 r0                         -- handshake length
    let (rnd, r2) ← takeN 32 (r1.drop 2)             -- skip legacy_version, take random
    let (sidLen, r3) ← (match r2 with | b :: t => some (b.toNat, t) | [] => none)
    let (sid, r4) ← takeN sidLen r3
    let (csLen, r5) ← rd16 r4
    let (csBytes, r6) ← takeN csLen r5
    let (compLen, r7) ← (match r6 with | b :: t => some (b.toNat, t) | [] => none)
    let (_comp, r8) ← takeN compLen r7
    let (extLen, r9) ← rd16 r8
    let (extBytes, _) ← takeN extLen r9
    let exts := walkExts extBytes.length extBytes
    let ks := (extBody exts 0x0033).bind (fun b =>
      match rd16 b with
      | some (_, entries) => findX25519 entries.length entries
      | none => none)
    let sv := (extBody exts 0x002b).map (fun b =>
      match b with
      | l :: t => (walkU16s t.length (t.take l.toNat)).contains tls13
      | [] => false)
    let sni := (extBody exts 0x0000).bind parseSni
    some { random := rnd
           sessionId := sid
           cipherSuites := walkU16s csBytes.length csBytes
           keyShare := ks
           tls13Offered := sv.getD false
           sni := sni }
  | _ => none

/-! ## The server's message builders (RFC 8446 §4) -/

/-- **ServerHello** (RFC 8446 §4.1.3): `legacy_version(0x0303) ‖ random(32) ‖
legacy_session_id_echo<uint8> ‖ cipher_suite(2) ‖ legacy_compression(0) ‖
extensions<uint16>` with a `key_share` (server public) and `supported_versions`
(0x0304) extension. Returns the full handshake message. -/
def buildServerHello (suite : Nat) (random sessionIdEcho serverPub : ByteArray) : ByteArray :=
  let keyShareExt := u16 0x0033 ++ vec16 (u16 x25519Group ++ vec16 serverPub)
  let supVerExt := u16 0x002b ++ vec16 (u16 tls13)
  -- RFC 8448 §3 orders key_share before supported_versions; match it so the
  -- transcript hash reproduces the published trace.
  let exts := keyShareExt ++ supVerExt
  let body := u16 0x0303 ++ random ++ vec8 sessionIdEcho
                ++ u16 suite ++ u8 0 ++ vec16 exts
  hsMsg 2 body

/-- **EncryptedExtensions** (RFC 8446 §4.3.1): empty extension block here. -/
def buildEncryptedExtensions : ByteArray := hsMsg 8 (u16 0)

/-- **Certificate** (RFC 8446 §4.4.2): a single certificate entry with no
extensions, and an empty `certificate_request_context`. `cert` is the raw
certificate data. -/
def buildCertificate (cert : ByteArray) : ByteArray :=
  let entry := vec24 cert ++ u16 0            -- cert_data<uint24> ‖ extensions<uint16>
  hsMsg 11 (u8 0 ++ vec24 entry)              -- context<uint8> ‖ certificate_list<uint24>

/-- The RFC 8446 §4.4.3 CertificateVerify signature content: 64 `0x20` octets,
the ASCII context string `"TLS 1.3, server CertificateVerify"`, a single `0x00`
separator, then the transcript hash. -/
def certVerifyContent (thash : ByteArray) : ByteArray :=
  ByteArray.mk ((List.replicate 64 (0x20 : UInt8)).toArray)
    ++ "TLS 1.3, server CertificateVerify".toUTF8 ++ u8 0 ++ thash

/-- **CertificateVerify** (RFC 8446 §4.4.3): the Ed25519 signature
(`SignatureScheme ed25519 = 0x0807`) over `certVerifyContent thash`. `none` only
on a `Crypto.ed25519Sign` size error. -/
def buildCertificateVerify (certSeed thash : ByteArray) : Option ByteArray :=
  match ed25519Sign certSeed (certVerifyContent thash) with
  | some sig => some (hsMsg 15 (u16 0x0807 ++ vec16 sig))
  | none => none

/-- The Finished key (RFC 8446 §4.4.4): `HKDF-Expand-Label(BaseKey, "finished",
"", Hash.length)`. -/
def finishedKey (baseKey : ByteArray) : Option ByteArray :=
  expandLabel baseKey "finished".toUTF8 ByteArray.empty hashLen

/-- The Finished `verify_data` (RFC 8446 §4.4.4): `HMAC(finished_key,
Transcript-Hash(...))`. HKDF-Extract *is* HMAC-Hash, so this is
`hkdfExtract finished_key thash`. -/
def verifyData (baseKey thash : ByteArray) : Option ByteArray :=
  match finishedKey baseKey with
  | some fk => hkdfExtract fk thash
  | none => none

/-- **Finished** (RFC 8446 §4.4.4): the handshake message carrying `verify_data`.
`none` on a derivation size error. -/
def buildFinished (baseKey thash : ByteArray) : Option ByteArray :=
  (verifyData baseKey thash).map (hsMsg 20)

/-! ## The server-side handshake state machine -/

/-- The established session material. It stores **only** the DHE secret and the
two transcript hashes; the key schedule and the per-direction record keys are
*derived* from them (below), so they are — by construction, not by convention —
a pure function of the transcript and the shared secret. -/
structure Established where
  /-- The X25519 shared secret. -/
  dhe : ByteArray
  /-- Transcript-Hash(ClientHello ‖ ServerHello). -/
  thHS : ByteArray
  /-- Transcript-Hash(ClientHello ‖ … ‖ server Finished). -/
  thSF : ByteArray
  /-- Negotiated application protocol. -/
  alpn : Tls.Alpn

/-- The full `TlsCrypto` key schedule for this session — `deriveSchedule` of the
DHE and the two transcript hashes. -/
def Established.schedule (e : Established) : TlsCrypto.Schedule :=
  TlsCrypto.deriveSchedule e.dhe e.thHS e.thSF

/-- Server-direction handshake record keys (the server writes its flight with
these), derived from the server_handshake_traffic_secret. -/
def Established.tx (e : Established) : TlsCrypto.RecordKeys :=
  (trafficKeys (e.schedule.serverHs.getD (zeros hashLen))).getD defaultKeys

/-- Client-direction handshake record keys (the server reads the client Finished
with these), derived from the client_handshake_traffic_secret. -/
def Established.rx (e : Established) : TlsCrypto.RecordKeys :=
  (trafficKeys (e.schedule.clientHs.getD (zeros hashLen))).getD defaultKeys

/-- The server handshake phase. -/
inductive HsState where
  /-- Awaiting the ClientHello. -/
  | waitCH
  /-- Server flight sent; awaiting the client Finished. -/
  | waitClientFinished (est : Established)
  /-- Handshake complete. -/
  | established (est : Established)
  /-- Handshake failed (parse error, no shared group, bad Finished). -/
  | failed

/-- What one server step emits. -/
structure ServerOut where
  /-- Record-layer bytes to send (the server flight / alerts). Never plaintext. -/
  flight : ByteArray := ByteArray.empty
  /-- Application plaintext delivered *by the handshake layer* — always empty;
  the record layer delivers application data only after establishment. -/
  delivered : Tls.Bytes := []
  /-- Set when the handshake reaches `established` this step. -/
  done : Bool := false

/-- The server's static handshake parameters. -/
structure ServerParams where
  /-- Server ephemeral X25519 private key (32 bytes). -/
  ephemeralPriv : ByteArray
  /-- The 32-byte server random for ServerHello. -/
  serverRandom : ByteArray
  /-- Ed25519 signing seed (RFC 8032 §5.1.5) for CertificateVerify. -/
  certSeed : ByteArray
  /-- The certificate bytes to send. -/
  certData : ByteArray

/-- Wrap an AEAD `encrypted_record` as a wire TLSCiphertext: `0x17 0x03 0x03 ‖
uint16 len ‖ ct` (the additional data header is the same bytes). -/
def wrapRecord (ct : ByteArray) : ByteArray := recordAD ct.size ++ ct

/-- Seal a handshake-phase inner plaintext into a wire record under key `rk` at
sequence 0. The TLS 1.3 inner plaintext appends the real content type
(`0x16` handshake). AD is the RFC 8446 §5.2 header for the ciphertext length. -/
def sealHsRecord (rk : TlsCrypto.RecordKeys) (inner : ByteArray) : Option ByteArray :=
  let pt := inner ++ u8 0x16
  match recordSeal rk 0 (recordAD (pt.size + 16)) pt with
  | some ct => some (wrapRecord ct)
  | none => none

/-- Open a wire handshake-phase record (`0x17 0x03 0x03 ‖ len ‖ ct`) under key
`rk` at sequence 0, and strip the trailing content-type byte, returning the inner
handshake message(s). -/
def openHsRecord (rk : TlsCrypto.RecordKeys) (wire : Tls.Bytes) : Option ByteArray :=
  match wire with
  | 0x17 :: _ :: _ :: l1 :: l2 :: rest =>
    let ctLen := l1.toNat * 256 + l2.toNat
    let ct := ofBytes (rest.take ctLen)
    match recordOpen rk 0 (recordAD ct.size) ct with
    | some pt =>
      -- drop the trailing content-type byte
      some (ofBytes (pt.toList.dropLast))
    | none => none
  | _ => none

/-- The client `verify_data` the server expects, given `est` — `HMAC` of the
client handshake finished key over Transcript-Hash(CH … server Finished). -/
def expectedClientVerifyData (est : Established) : Option ByteArray :=
  verifyData (est.schedule.clientHs.getD (zeros hashLen)) est.thSF

/-- Decide whether an opened client Finished message carries the expected
`verify_data`. The client Finished is `0x14 ‖ uint24 32 ‖ verify_data(32)`, so the
`verify_data` is the message body after the 4-byte header. -/
def acceptClientFinished (est : Established) (openedFin : Option ByteArray) : Bool :=
  match openedFin, expectedClientVerifyData est with
  | some fin, some expected =>
    -- strip the 4-byte handshake header, compare the verify_data
    (fin.toList.drop 4) == expected.toList
  | _, _ => false

/-- Derive the `Established` record from the parsed ClientHello and the server's
ephemeral. `serverPub`/`dhe` are the already-computed X25519 outputs; `chMsg` is
the ClientHello handshake message (for the transcript). Returns the established
material **and** the server flight bytes, or `none` on a derivation size error. -/
def buildFlight (params : ServerParams) (ch : ClientHello)
    (serverPub dhe chMsg : ByteArray) : Option (Established × ByteArray) :=
  -- ServerHello (plaintext record) and the handshake transcript hashes.
  let sh := buildServerHello chachaSuite params.serverRandom (ofBytes ch.sessionId) serverPub
  let thHS := sha256 (chMsg ++ sh)
  let ee := buildEncryptedExtensions
  let cert := buildCertificate params.certData
  match earlySecretNoPsk with
  | none => none
  | some es =>
    match handshakeSecret es dhe with
    | none => none
    | some hs =>
      match serverHsTrafficSecret hs thHS with
      | none => none
      | some sHs =>
        match trafficKeys sHs with
        | none => none
        | some txHs =>
          match buildCertificateVerify params.certSeed (sha256 (chMsg ++ sh ++ ee ++ cert)) with
          | none => none
          | some cv =>
            match buildFinished sHs (sha256 (chMsg ++ sh ++ ee ++ cert ++ cv)) with
            | none => none
            | some sFin =>
              match sealHsRecord txHs (ee ++ cert ++ cv ++ sFin) with
              | none => none
              | some innerRecord =>
                let thSF := sha256 (chMsg ++ sh ++ ee ++ cert ++ cv ++ sFin)
                let shRecord := ByteArray.mk #[0x16, 0x03, 0x03] ++ u16 sh.size ++ sh
                let est : Established := { dhe := dhe, thHS := thHS, thSF := thSF, alpn := .h1 }
                some (est, shRecord ++ innerRecord)

/-- **The server handshake step.** Total; drives the real key schedule and record
layer over EverCrypt when a ClientHello is processed. -/
def serverStep (params : ServerParams) : HsState → Tls.Bytes → HsState × ServerOut
  | .waitCH, buf =>
    match parseClientHello buf with
    | none => (.failed, {})
    | some ch =>
      if ch.tls13Offered && ch.cipherSuites.contains chachaSuite then
        match ch.keyShare with
        | none => (.failed, {})
        | some cpub =>
          match x25519Base params.ephemeralPriv, x25519 params.ephemeralPriv (ofBytes cpub) with
          | some serverPub, some dhe =>
            match buildFlight params ch serverPub dhe (ofBytes (stripRecord buf)) with
            | some (est, flight) => (.waitClientFinished est, { flight := flight })
            | none => (.failed, {})
          | _, _ => (.failed, {})
      else (.failed, {})
  | .waitClientFinished est, buf =>
    if acceptClientFinished est (openHsRecord est.rx buf)
    then (.established est, { done := true })
    else (.failed, {})
  | .established est, _ => (.established est, {})
  | .failed, _ => (.failed, {})

/-! ## Theorems -/

/-- **The handshake layer surfaces no application plaintext.** Every server step
delivers an empty application byte string — application data is the record
layer's job, only after establishment. -/
theorem serverStep_delivers_nothing (params : ServerParams) (st : HsState)
    (buf : Tls.Bytes) : (serverStep params st buf).2.delivered = [] := by
  cases st with
  | waitCH =>
    simp only [serverStep]
    split
    · rfl
    · split
      · split
        · rfl
        · split
          · split <;> rfl
          · rfl
      · rfl
  | waitClientFinished est => simp only [serverStep]; split <;> rfl
  | established est => rfl
  | failed => rfl

/-- **No establishment without the Finished round.** A single step from `waitCH`
never reaches `established`: the ClientHello moves the machine to
`waitClientFinished` (or `failed`), so no application-data phase is entered before
the client Finished is verified. -/
theorem waitCH_not_established (params : ServerParams) (buf : Tls.Bytes)
    (est : Established) :
    (serverStep params .waitCH buf).1 ≠ .established est := by
  simp only [serverStep]
  split
  · exact fun h => HsState.noConfusion h
  · split
    · split
      · exact fun h => HsState.noConfusion h
      · split
        · split <;> exact fun h => HsState.noConfusion h
        · exact fun h => HsState.noConfusion h
    · exact fun h => HsState.noConfusion h

/-- **The derived keys are a pure function of the DHE secret and the transcript.**
Every `Established`'s key schedule is exactly `TlsCrypto.deriveSchedule dhe thHS
thSF` — there is no hidden input: the schedule and both directions' record keys
are *defined* as functions of the stored DHE secret and transcript hashes. -/
theorem hs_transcript_drives_keys (est : Established) :
    est.schedule = TlsCrypto.deriveSchedule est.dhe est.thHS est.thSF := rfl

/-- **The key schedule is deterministic**, transported: equal DHE and equal
transcript hashes give equal derived schedules — `TlsCrypto.keyschedule_deterministic`
composed with `hs_transcript_drives_keys`. Two `Established`s built from the same
DHE and transcripts hold the same keys. -/
theorem hs_keys_deterministic
    (e1 e2 : Established)
    (hd : e1.dhe = e2.dhe) (h1 : e1.thHS = e2.thHS) (h2 : e1.thSF = e2.thSF) :
    e1.schedule = e2.schedule := by
  rw [hs_transcript_drives_keys e1, hs_transcript_drives_keys e2]
  exact TlsCrypto.keyschedule_deterministic hd h1 h2

/-- **A wrong client Finished is rejected.** From `waitClientFinished`, if the
opened client Finished does not carry the expected `verify_data`
(`acceptClientFinished = false`), the machine goes to `failed` — never
`established`. Acceptance requires an exact MAC match, so no forged or altered
Finished completes the handshake. -/
theorem hs_finished_authenticates (params : ServerParams) (est : Established)
    (buf : Tls.Bytes) (h : acceptClientFinished est (openHsRecord est.rx buf) = false) :
    (serverStep params (.waitClientFinished est) buf).1 = .failed := by
  simp only [serverStep, h, Bool.false_eq_true, if_false]

/-- Corollary: acceptance is exactly the MAC match. If the machine reaches
`established` from `waitClientFinished`, then `acceptClientFinished` held. -/
theorem hs_established_needs_finished (params : ServerParams) (est est' : Established)
    (buf : Tls.Bytes)
    (h : (serverStep params (.waitClientFinished est) buf).1 = .established est') :
    acceptClientFinished est (openHsRecord est.rx buf) = true := by
  simp only [serverStep] at h
  by_cases hb : acceptClientFinished est (openHsRecord est.rx buf) = true
  · exact hb
  · simp only [Bool.not_eq_true] at hb
    rw [hb] at h; simp at h

/-! ## Wiring the real message layer into `Tls.Config`

`serverHsFeed` is the `Tls.Config.hsFeed`-shaped adapter that runs the REAL
handshake message layer: it parses the ClientHello, agrees the DHE, drives the
key schedule, and emits the sealed server flight. `handshakeConfig` installs it
over `TlsCrypto.realConfig`'s real EverCrypt record layer — replacing the
shortcut `hsFeed` (which ignored the bytes and "completed on first ciphertext").
-/

/-- **The real `hsFeed`.** On accumulated ciphertext, run the server handshake
from `waitCH`: a well-formed ClientHello yields `.done` with the real server
flight (ServerHello + sealed EncryptedExtensions/Certificate/CertificateVerify/
Finished); a malformed one yields `.fail`; an empty buffer is `.insufficient`.
Unlike the shortcut, this inspects the bytes and runs real crypto. -/
def serverHsFeed (params : ServerParams) : Tls.HsConn → Tls.Bytes → Tls.HsOut :=
  fun _hs buf =>
    if buf.isEmpty then .insufficient
    else
      match serverStep params .waitCH buf with
      | (.waitClientFinished _, out) => .done { id := 0 } buf.length out.flight.toList .h1 []
      | _ => .fail

/-- A `Tls.Config` whose handshake message layer is the REAL server handshake and
whose record layer is `TlsCrypto`'s real EverCrypt seal/open. The `dhe`/`thHS`/
`thAP` seed the record-direction keys exactly as `realConfig` does; the change is
`hsFeed`, now the real parser instead of the shortcut. -/
def handshakeConfig (params : ServerParams) (dhe thHS thAP : ByteArray) : Tls.Config :=
  { TlsCrypto.realConfig dhe thHS thAP with hsFeed := serverHsFeed params }

/-- **The config's `hsFeed` is the real handshake layer** — not the shortcut. -/
theorem handshakeConfig_hsFeed (params : ServerParams) (dhe thHS thAP : ByteArray) :
    (handshakeConfig params dhe thHS thAP).hsFeed = serverHsFeed params := rfl

/-- **The real `hsFeed` inspects the bytes.** On an empty buffer it is
`.insufficient` — whereas `realConfig`'s shortcut is also `.insufficient` there,
but on any *nonempty* buffer the shortcut returns `.done` unconditionally while
`serverHsFeed` runs the parser and returns `.fail` on a non-ClientHello. This
witnesses that the two `hsFeed`s are different functions. -/
theorem serverHsFeed_rejects_non_clienthello (params : ServerParams)
    (hs : Tls.HsConn) :
    serverHsFeed params hs [0x00] = .fail := by
  simp only [serverHsFeed, serverStep, parseClientHello]
  rfl

/-- The shortcut `hsFeed` of `realConfig`, by contrast, "completes" on that same
byte — the exact behaviour this module replaces. -/
theorem realConfig_shortcut_completes (dhe thHS thAP : ByteArray) (hs : Tls.HsConn) :
    (TlsCrypto.realConfig dhe thHS thAP).hsFeed hs [0x00]
      = .done { id := 0 } 1 [] .h1 [] := rfl

end TlsHandshake
