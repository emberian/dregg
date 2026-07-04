# QUIC transport handshake + packet protection over verified crypto

`QuicTransport.lean` closes a gap in the connection
FSM (`Quic/Fsm.lean`) is *sans-IO* and takes packets "already decrypted and
parsed" (`Quic.Input.pktReceived`), so the transport cryptography that turns UDP
bytes into those packets was stubbed. No off-the-shelf QUIC client could
handshake against the orb, because there was no key schedule and no packet
protection on the wire.

This module supplies that missing transport layer, computed over the **same
EverCrypt primitives** (`Crypto.lean`, HACL*/EverCrypt, verified in F*) the TLS
record layer already runs on, and mirroring `TlsCrypto.lean` — because RFC 9001
says QUIC *reuses* the TLS 1.3 key schedule.

## What is modeled (and verified)

1. **Initial-secret derivation — RFC 9001 §5.2.** `initial_secret =
   HKDF-Extract(initial_salt, DCID)` over `Crypto.hkdfExtract`, then the
   client/server initial secrets via `HKDF-Expand-Label`. QUIC's
   `HKDF-Expand-Label` is bit-for-bit the TLS one (same `"tls13 "` prefix), so
   `TlsCrypto.expandLabel` is reused unchanged.

2. **Packet-protection keys — RFC 9001 §5.1.** `key`/`iv`/`hp` per encryption
   level via `HKDF-Expand-Label` under the `"quic key"`/`"quic iv"`/`"quic hp"`
   labels. Cipher-independent HKDF output (16-byte keys for AES-128-GCM, 32-byte
   for ChaCha20-Poly1305; 12-byte iv always).

3. **AEAD payload protection — RFC 9001 §5.3.** Per-packet nonce = packet number
   XORed into the write-IV (identical to `TlsCrypto.recordNonce`); AAD = the QUIC
   header; seal/open = `Crypto.chachaSeal`/`chachaOpen`
   (TLS_CHACHA20_POLY1305_SHA256, a QUIC v1 cipher suite).

4. **The handshake key transition** Initial → Handshake → 1-RTT (RFC 9001 §4, §7)
   as a monotone key-installation machine: levels install in order, never
   uninstall, and 1-RTT keys are gated on Handshake keys being present.

## Theorems (`lake` accepts; zero sorries)

| theorem | statement |
|---|---|
| `quic_initial_keys_real` | the initial secrets are a pure function of DCID (+ the fixed salt) via real HKDF — equal DCID ⇒ equal secrets. Mirrors `TlsCrypto.keyschedule_deterministic`. |
| `quic_packet_roundtrip` | seal then open under the same key/pn/header recovers the payload. Transported from `Crypto.Assumptions.chacha_open_seal_roundtrip`. |
| `quic_packet_forgery_fails` | a payload that is not the genuine sealing of `pt` never opens to `pt`. Transported from `Crypto.Assumptions.chacha_open_authentic`. |
| `quic_no_1rtt_before_handshake` | with no handshake-key install in the event stream, no 1-RTT packet is ever accepted (`acceptOneRtt … = none`). The key-schedule sibling of `Quic.no_appdata_before_established`. |
| `quic_1rtt_requires_handshake` / `KeyState.run_wf` | the level-ordering invariant (1-RTT keys ⇒ Handshake keys) holds in every reachable state. |

`#print axioms` for these is `{propext, Quot.sound}` plus, for the AEAD ones, the
named crypto axioms `Crypto.Assumptions.chacha_open_seal_roundtrip` /
`chacha_open_authentic` — the functional shadows of EverCrypt's F* AEAD proofs.
No other axioms; no sorries.

## Self-test — observed on live EverCrypt

`QuicTransport.SelfTest.main` (compiled as an exe linking `ffi/crypto_shim.o` +
`libevercrypt.a`, the `tls-keyschedule-selftest` recipe) checks the derivations
against the **RFC 9001 Appendix A.1** test vectors and runs a real ChaCha20
packet roundtrip. Observed output (DCID `0x8394c8f03e515708`):

```
[PASS] A.1 HkdfLabel "client in"   [PASS] A.1 HkdfLabel "quic key"
[PASS] A.1 HkdfLabel "quic iv"     [PASS] A.1 HkdfLabel "quic hp"
[PASS] A.1 initial_secret            = 7db5df06…e9ed0a44
[PASS] A.1 client_initial_secret     = c00cf151…6c357aea
[PASS] A.1 server_initial_secret     = 3c199828…cdda951b
[PASS] A.1 client key/iv/hp          = 1f369613… / fa044b2f… / 9f50449e…
[PASS] A.1 server key/iv/hp          = cf3a5331… / 0ac1493c… / c206b8d9…
[PASS] ChaCha packet seal→open roundtrip (pn 2)
[PASS] open at wrong packet number → none
[PASS] tampered payload → none
[PASS] altered header (AAD) → none

all 17 QUIC transport vectors passed (RFC 9001 A.1 + ChaCha roundtrip)
```

Every A.1 hex value — secrets and per-level key/iv/hp — is reproduced by the real
HKDF over EverCrypt from the DCID alone. (The A.1 key/iv/hp are the AES-128-GCM
lengths the RFC uses; the derivation is cipher-independent HKDF, so they match
exactly even though the *AEAD* theorems above run on ChaCha20.)

### Build/run the self-test

Not wired into `lakefile.toml` (kept to the single owned file). To run it, either
add a `lean_exe` stanza mirroring `tls-keyschedule-selftest`, or link manually as
shown below:

```
lake env lean -c QuicTransport.c QuicTransport.lean
lake env leanc -c QuicTransport.c -o QuicTransport.o
lake env leanc QuicTransport.o \
  .lake/build/ir/{Crypto,TlsCrypto}.c.o.export \
  .lake/build/ir/Tls/{Basic,Step,Theorems}.c.o.export \
  .lake/build/ir/Quic/{Basic,Fsm}.c.o.export \
  ffi/crypto_shim.o \
  -L/path/to/hacl-star/dist/gcc-compatible -levercrypt \
  -o quic-selftest -Wl,-no_data_const
./quic-selftest
```

## Is a real QUIC handshake now modeled over verified crypto? — yes, the crypto core

The cryptographic transport — key schedule and AEAD payload protection — is
modeled and machine-checked over real EverCrypt, and reproduces the RFC 9001 A.1
vectors byte-for-byte. That is the part that was a stub. **A live off-the-shelf
client (`curl --http3`, quiche, ngtcp2) does not yet complete a handshake**,
because the following shell-side / adjacent pieces are still open. None require
re-proving crypto; they are wire glue and one crypto-seam addition.

1. **Header protection (RFC 9001 §5.4) — one missing primitive.** The `hp` *key*
   is derived here, but applying the mask needs a **raw block cipher**
   (ChaCha20 block, or AES-ECB) to turn a ciphertext sample into the 5-byte mask
   XORed into the first header byte + packet-number bytes. `Crypto.lean` exposes
   only AEAD, not a raw block. Adding `Crypto.chacha20Block` (a HACL* primitive)
   to the shim is a localized, named addition; the masking logic is then pure
   byte-shuffling statable in this file.

2. **AES-128-GCM for real Initial packets.** RFC 9001 Initial packets use
   AES-128-GCM. `Crypto` has AES-*256*-GCM and ChaCha20, not AES-128. Decrypting
   an off-the-shelf client's *actual* Initial (A.2 ciphertext) needs AES-128-GCM
   in the shim — another named EverCrypt binding. The *key schedule* for it is
   already done and verified (A.1 passes).

3. **Wire parsing/serialization.** QUIC long/short headers, variable-length
   integers, packet-number truncation/decoding, coalesced packets, and frame
   parsing (esp. CRYPTO frames carrying the TLS handshake). The FSM consumes
   pre-parsed packets; this codec is the boundary between UDP bytes and
   `Quic.Input`.

4. **Driving the TLS 1.3 handshake.** `TlsHandshake.lean` already models the
   server handshake message layer and derives the handshake/application traffic
   secrets. Wiring: feed QUIC CRYPTO-frame payloads into it, then hand its
   derived secrets to `KeyState.step (.installHandshake …)` / `(.installOneRtt …)`
   to install the Handshake and 1-RTT keys this module protects packets with.

5. **UDP socket shell.** `ffi/mac_udp.c` already recv/sends datagrams for the H3
   datagram lane. The QUIC path would: recv → parse (item 3) → remove header
   protection (item 1) → `openPacket` (this module) → `Quic.step` (the FSM) →
   `sealPacket` + re-protect + send.

6. **Out of scope by design (unchanged):** Retry/version-negotiation, connection
   ID management, path validation, 0-RTT anti-replay (that lives in
   `Quic.Replay`), and loss/congestion control (RFC 9002 — the timing half, not
   representable without an explicit clock).

In one line: **the QUIC transport crypto is now real and verified against the RFC
vectors; a live handshake still needs the header-protection block primitive, an
AES-128-GCM seam binding, the wire codec, and the UDP shell to drive them.**
