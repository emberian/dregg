# QUIC-LIVE — real header protection, and a real QUIC client over the socket

This extends the QUIC-SOCKET path (`orb-quic`). Previously the server decrypted a
**crafted** Initial whose first byte and packet number were sent *in the clear*
(header protection dropped), protected with ChaCha20-Poly1305. This closes
the header-protection gap and drives a **real off-the-shelf QUIC client**
(aioquic) at the server over a real UDP socket.

Two things are new:

1. **Real header protection (RFC 9001 §5.4).** The receiver now removes header
   protection before it can even know how many packet-number bytes there are —
   the packet-number length lives in the header-protected low bits of the first
   byte. The mask is derived from a 16-byte ciphertext sample with the ChaCha20
   block function (RFC 9001 §5.4.4), and the truncated packet number is decoded
   (RFC 9000 §A.3).

2. **A real client over the socket.** aioquic (1.3.0) — an independent QUIC
   implementation whose crypto is OpenSSL-backed — is pointed at `orb-quic` two
   ways: (a) its own crypto engine seals + header-protects an Initial that the
   Lean/EverCrypt server removes and dispatches (byte-for-byte cross-impl
   agreement), and (b) a full `QuicConnection.connect()` sends a spec Initial and
   we report exactly how far it gets.

## What was missing, and the one new verified crossing

Header protection needs a **raw block-cipher keystream**, not an AEAD. The
verified `Crypto` seam exposed only ChaCha20-*Poly1305* (the AEAD), so the mask
could not be computed. Exactly one new `@[extern]` supplies it:

```
QuicHeaderProt.chacha20Raw : key(32) iv(12) (ctr : UInt32) src → Option ByteArray
```

bound (`drorb_chacha20`, in `ffi/mac_udp.c`) to **`EverCrypt_Cipher_chacha20`** —
the same portable, F*-verified HACL* ChaCha20 the ChaCha20-Poly1305 AEAD itself
runs on this host. Feeding a zero `src` yields the raw keystream, i.e. the
header-protection mask (RFC 9001 §5.4.4: `counter = sample[0..4]` little-endian,
`nonce = sample[4..16]`). Its assumed property (`chacha20Raw_valid`) is only that
it is total and length-preserving on valid sizes — a keystream XOR; no secrecy
claim is attached to this XOR (header protection's security is the AEAD's).

`QuicHeaderProt.xor_mask_involutive` (`(b ^^^ m) ^^^ m = b`, axioms `{propext,
Quot.sound}`) is the algebraic fact that apply-and-remove header protection are
the same operation. The sample is fixed at `pn_offset + 4`, strictly after the
≤4 masked packet-number bytes, so masking never perturbs its own sample.

## AES-128-GCM Initial: the honest residual (arm64, no AES-NI)

RFC 9001 §5.2 fixes the QUIC v1 **Initial** cipher to **AES-128-GCM** with
**AES-ECB** header protection — this is not negotiable, and every real client's
first flight uses it. On this host that path is unavailable:

* This machine is **arm64** (`uname -m → arm64`); `EverCrypt_AutoConfig2` reports
  `has_aesni=0 has_pclmulqdq=0`.
* EverCrypt's only AES-GCM is the **Vale x86-64** assembly; on arm64
  `EverCrypt_AEAD_encrypt_expand_aes128_gcm` returns `UnsupportedAlgorithm`
  (probed directly: `rc=1`). There is no portable/bitsliced AES in this
  `libevercrypt.a` build (only the Vale symbols).

So AES-128-GCM AEAD and AES-ECB header protection cannot run here with the
verified crypto, and adding an **unverified** C AES to the trusted crypto base is
exactly the kind of TCB regression this project refuses. The AES-128-GCM key
*schedule* is nonetheless fully available and vector-correct: `QuicTransport`'s
self-test already checks the RFC 9001 A.1 AES-128 client key
(`1f369613dd76d5467730efcbe3b1a22d`), iv, and hp against live EverCrypt HKDF. What
is blocked is only the AES *cipher execution*, named precisely as the residual.

The server therefore runs the **ChaCha20** QUIC cipher suite end-to-end (a real QUIC
v1 suite — the one used for 1-RTT after negotiation) with real header protection,
and reports the AES Initial residual honestly, rather than faking a decrypt.

## Observed — cross-implementation decrypt over the socket

`aioquic`'s own `CryptoContext` (ChaCha20-Poly1305 suite), keyed from the DCID via
RFC 9001 §5.2, seals + header-protects an Initial and sends it to `orb-quic`:

```
[client] DCID           = 8394c8f03e515708
[client] client_initial = c00cf151ca5be075ed0ebfb5c80323c42d6b7db67881289af4008f1f6c357aea
[client] aioquic-sealed+HP-protected packet (46 bytes):
         c700000001088394c8f03e5157080000401c4dc1368043d2d63cc91a4c05710b55f23a9875b7cb49f80d43cd3de1
[client] wire first byte = 0xc7 (unprotected 0xc3)
[client] SERVER RESPONSE (73 bytes): b'HTTP/1.1 403 Forbidden\r\nContent-Length: 27\r\n\r\npolicy: undeclared surface\n'
[client] RESULT: cross-implementation decrypt+dispatch CONFIRMED over the socket
```

Server side (the untrusted C shell logging the seam crossing):

```
orb-quic/udp: recv 46 bytes -> Lean callback -> 73 bytes (decrypted+dispatched, sending response)
```

Two facts fall out of this transcript:

* `client_initial` is exactly the RFC 9001 A.1 client initial secret
  (`c00cf151…`) — both sides ran the standard key schedule.
* The 46-byte aioquic packet is **byte-for-byte identical** to the one the Lean
  in-process self-test crafts on EverCrypt (same hex, wire first byte `0xc7`). An
  independent OpenSSL-backed implementation and the Lean/EverCrypt one produce the
  *same* header-protected + AEAD-sealed wire bytes, and the server removes header
  protection (recovering first byte `0xc3`, pnLen 4, pn 1), AEAD-opens the STREAM
  frame, and drives the **proven** H3 dispatch to an HTTP response (the demo
  policy's `403`; the response is a real product of the guarded pipeline).

The in-process self-test (`orb-quic` startup) shows the same path:

```
[craft] HP-protected Initial packet (46 bytes): c70000000108…d43cd3de1
[locate] dcid=8394c8f03e515708 pnOff=18 pkt=46B
[unprotect] HP removed: firstByte=0xc3 pnLen=4 pn=1
[decrypt] openPacket OK at pn=1, plaintext 8B: 080001040000d1c1
[dispatch] H3 served, response 73B, starts: "HTTP/1.1 403 Forbidden\x0d\n…"
── self-test PASSED ──
```

## Observed — a real spec client, and how far it gets

`aioquic`'s `QuicConnection.connect()` generates a spec-compliant Initial flight
(AES-128-GCM, AES-ECB header protection, a ClientHello in a CRYPTO frame, padded
to 1200 bytes) and sends it:

```
[real-client] aioquic Initial datagram (1200 bytes) first byte 0xc3
[real-client] first 32 bytes: c30000000108 3daee01e9e224fd6 08eba1ea3240589c910041daf9afa710d022
[real-client] sent 1 datagram(s) — a spec AES-128-GCM Initial
[real-client] no response — server could not remove AES-128-GCM protection
```

Server: `orb-quic/udp: recv 1200 bytes -> Lean callback -> 0 bytes (dropped: parse/AEAD-auth failure, no reply)`.

Running that captured real datagram through the **actual server parse**
(`orb-quic --diag`, which calls `locateInitial`/`openInitial` — the same code the
socket loop runs) shows precisely how far it gets:

```
[diag] datagram 1200 bytes, first byte 0xc3
[diag] locateInitial OK — long-header Initial recognized; DCID=3daee01e9e224fd6, pnOff=26
[diag] openInitial: header-protection/AEAD removal returned none.
[diag] RESIDUAL: this Initial is AES-128-GCM (AEAD) + AES-ECB (header protection),
       the RFC 9001 §5.2 mandated Initial cipher … this host is arm64, so AES is
       unavailable and the ChaCha20 keys/mask the server derived do not match.
```

So the server **receives** a real off-the-shelf client's spec Initial over the
socket, **parses its long header and extracts the DCID**, then stops at exactly
the AES-128-GCM / AES-ECB step, which no verified primitive on this arm64 host can
perform.

## The residual to a full 1-RTT handshake (named)

Even with AES available, a full handshake needs more than decrypting the client
Initial. The client's Initial carries a **ClientHello in a CRYPTO frame**; the
server must **respond with its own flight** — a server Initial (ServerHello in a
CRYPTO frame) plus a Handshake-level flight (EncryptedExtensions, Certificate,
CertificateVerify, Finished) — installing Handshake then 1-RTT keys before any H3
request arrives. Those pieces exist in the tree (`TlsHandshake`, and
`QuicTransport.KeyState`'s Initial→Handshake→1-RTT install machine with
`quic_no_1rtt_before_handshake`), but wiring them into a live responding QUIC
server is the residual beyond this path. What is demonstrated here is the ingress
half: real header protection removed and a real-QUIC-library packet decrypted and
dispatched over the socket, with the server response flight named as the
outstanding work.

## Files / build

* `QuicHeaderProt.lean` — the `chacha20Raw` extern, the ChaCha20 header-protection
  mask, truncated-PN decode, apply/remove header protection, and the XOR
  involution theorem.
* `IoQuic.lean` — `locateInitial` (parse to the header-protected PN), `openInitial`
  (derive keys → remove header protection → AEAD-open), the header-protected
  `craftInitial`, the self-test, and `--diag`.
* `ffi/mac_udp.c` — adds `drorb_chacha20` (→ `EverCrypt_Cipher_chacha20`), guarded
  by `#if __has_include("EverCrypt_Cipher.h")`.

`mac_udp.o` must be compiled **with** the EverCrypt include path for the
`drorb_chacha20` symbol (the plain `ffi/build-mac-multi.sh` omits it and the guard
drops the function):

```
inc="$(lake env lean --print-prefix)/include"; HACL=/opt/hacl-star/dist/gcc-compatible; KRML=/opt/hacl-star/dist/karamel
cc -c -O2 -fPIC -I "$inc" -I "$HACL" -I "$KRML/include" -I "$KRML/krmllib/dist/minimal" -o ffi/mac_udp.o ffi/mac_udp.c
lake build orb-quic          # links crypto_shim.o + libevercrypt.a
```

`orb-quic` and `orb-mac-multi` both build green; zero sorries; the new theorems'
axioms are `{propext, Quot.sound}`, and `chacha20Raw_valid` is a named EverCrypt
shim property alongside the existing `Crypto.Assumptions`.

## Reproduce the live tests

```
pip install aioquic                       # 1.3.0 used here
./.lake/build/bin/orb-quic 18443 &        # self-test + live socket
python test1_chacha.py 18443              # aioquic ChaCha cross-impl → 403 dispatched
python test2_realclient.py 18443          # real spec AES-128-GCM Initial → dropped (residual)
./.lake/build/bin/orb-quic --diag real_initial.hex   # server parse of the real Initial
```
