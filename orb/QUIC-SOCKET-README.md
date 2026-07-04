# QUIC SOCKET-LIVE — a real QUIC Initial packet, decrypted by verified EverCrypt over a real UDP socket, into the proven H3 dispatch

Previously the UDP path (`orb-mac-multi`, `ffi/mac_udp.c` +
`IoMacMulti.udpHandle`) took each datagram's bytes as **already-decrypted**
application data: the proven datagram model (`Reactor.Quic.DatagramEvent`) assumes
a packet arrives "pre-parsed and pre-decrypted", so no packet protection ran on the
wire. This closes that gap for the QUIC **Initial** packet: a real UDP datagram is
a QUIC long-header Initial whose protected payload is **DECRYPTED by the
verified EverCrypt QUIC packet protection** before it ever reaches the
proven `Reactor.QuicIngress.datagramServe`.

## What runs

`orb-quic` (new `lean_exe`, root `IoQuic.lean`) — the callback `quicDatagram :
ByteArray → ByteArray` fed to the untrusted UDP shell `ffi/mac_udp.c`:

1. **parse** the QUIC long-header Initial packet (RFC 9000 §17.2.2) — extract the
   Destination Connection ID, the packet number, the unprotected header (the AEAD
   additional data), and the protected payload (`ciphertext ‖ tag`);
2. **derive** the Initial keys from the DCID — `HKDF-Extract(initial_salt, DCID)`
   then `HKDF-Expand-Label(…,"client in"/"quic key"/"quic iv")` — real HKDF-SHA256
   over HACL\*/EverCrypt;
3. **decrypt** the payload with real EverCrypt ChaCha20-Poly1305 AEAD open, at the
   RFC 9001 §5.3 per-packet nonce (`iv XOR pn`), with the QUIC header as AAD;
4. **dispatch** — recover the QUIC STREAM frame's H3 bytes and feed them to the
   proven `datagramServe` (real `Quic.step` + `H3.decFrame` +
   `H3.Qpack.decodeFieldSection` + `RingSubmission.dispatch`), then serve through
   the same proven guarded pipeline the TCP paths run
   (`Reactor.Ingress.serveOverSubs`);
5. **respond** — return the HTTP response bytes, which the C shell `sendto`s back.

The proven core stands alone: `Reactor/QuicIngress.lean`, `QuicTransport.lean`,
`Crypto.lean`, `TlsCrypto.lean` are not modified by the bridge;
`quic_ingress_dispatch` depends only on `[propext, Classical.choice,
Quot.sound]`. The bridge is `IoQuic.lean` (the QUIC↔socket bridge), `ffi/mac_udp.c`
(per-datagram logging around the recv→callback→send loop), and the `orb-quic`
entry in `lakefile.toml`.

### The crypto is the QuicTransport derivations, verbatim, on the same EverCrypt

`IoQuic` re-expresses `QuicTransport.initialSecrets/deriveChachaKeys/openPacket`
directly over the **same** verified primitives QuicTransport is built from —
`Crypto.hkdfExtract`, `TlsCrypto.expandLabel`, `TlsCrypto.recordNonce`,
`Crypto.chachaOpen`/`chachaSeal` (→ HACL\*/EverCrypt, F\*-verified). It does not
`import QuicTransport` because `QuicTransport.lean` ships a trailing orphan `def
main : IO UInt32` (its inline self-test, wired to no `lean_exe`) that collides with
this exe's `_root_.main`; resolving that would require editing `QuicTransport.lean`,
which is out of scope here. The re-expression is validated to be the
identical computation two independent ways:

* the in-process `selfTest` and the running server both derive `client_secret =
  c00cf151ca5be075ed0ebfb5c80323c42d6b7db67881289af4008f1f6c357aea`, the exact
  RFC 9001 Appendix A.1 vector `QuicTransport.SelfTest` asserts;
* the Python client (below) derives the same value from an **independent** RFC 9001
  implementation (`cryptography`'s HKDF + ChaCha20-Poly1305) and produces a
  byte-identical sealed packet, which EverCrypt then opens over the socket.

## Observed transcript (macOS, real UDP socket 127.0.0.1:8443)

### Server startup — in-process decrypt→dispatch on live EverCrypt

```
orb-quic: QUIC SOCKET-LIVE — verified EverCrypt packet protection → proven H3 dispatch
── in-process self-test (crafted Initial, live EverCrypt) ──
[craft] Initial packet (46 bytes): c300000001088394c8f03e5157080000401c0000000143d2d63cc91a4c05710b55f23a9875b7cb49f80d43cd3de1
[parse] dcid=8394c8f03e515708 pn=1 header=22B ct=24B
[decrypt] openPacket OK, plaintext 8B: 080001040000d1c1
[dispatch] H3 served, response 73B, starts: "HTTP/1.1 403 Forbidden\x0d\nContent-Length: "
── self-test PASSED ──
listening for real QUIC Initial datagrams on 127.0.0.1:8443 (Ctrl-C to stop)
orb-mac-multi: QUIC/UDP listening on 127.0.0.1:8443 (proven H3 datagram ingress over real UDP)
```

The decrypted plaintext `08 00 | 01 04 00 00 d1 c1` is a QUIC STREAM frame (type
`0x08`, stream id `0`) carrying the H3 HEADERS frame for `GET /`.

### Python client — independent RFC 9001 seal, sent over the wire

`scratchpad/quic_client.py` (derives keys via `hmac`/`hashlib` HKDF, seals with
`cryptography.ChaCha20Poly1305`, sends one UDP datagram):

```
[client] initial_secret = 7db5df06e7a69e432496adedb00851923595221596ae2ae9fb8115c1e9ed0a44
[client] client_secret  = c00cf151ca5be075ed0ebfb5c80323c42d6b7db67881289af4008f1f6c357aea
[client] quic key       = 9f81a6a9be9eaa9bdebb3ceba916a2c23d29d6fa91ac3cfb9804c56e41a654a5
[client] quic iv        = fa044b2f42a3fd3b46fb255c
[client] nonce          = fa044b2f42a3fd3b46fb255d
[client] AAD (header)    = c300000001088394c8f03e5157080000401c00000001
[client] sealed payload  = 43d2d63cc91a4c05710b55f23a9875b7cb49f80d43cd3de1
[client] full Initial packet (46 bytes): c300000001088394c8f03e5157080000401c0000000143d2d63cc91a4c05710b55f23a9875b7cb49f80d43cd3de1
[client] sent 46 bytes to 127.0.0.1:8443, awaiting response...
[client] RECEIVED 73 bytes from ('127.0.0.1', 8443):
---8<--- response ---8<---
HTTP/1.1 403 Forbidden
Content-Length: 27

policy: undeclared surface
---8<--- end ---8<---
```

The Python-sealed packet is byte-identical to the Lean-crafted one — two
independent implementations agree on the derived keys **and** the ChaCha20-Poly1305
ciphertext.

### Server log — the socket decrypt→dispatch, and the AEAD authenticity gate

```
orb-quic/udp: recv 46 bytes -> Lean callback -> 73 bytes (decrypted+dispatched, sending response)
orb-quic/udp: recv 46 bytes -> Lean callback -> 0 bytes (dropped: parse/AEAD-auth failure, no reply)
```

The first line is the Python client's valid packet: verified EverCrypt `openPacket`
authenticated and decrypted it, the H3 request dispatched, 73 response bytes went
back. The second line is a **tampered** packet (one ciphertext byte flipped) — the
EverCrypt AEAD tag check failed, `openPacket` returned `none`, and the server
dropped it with no reply. The authenticity is enforced by the verified crypto, not
bypassed.

### On the `403 Forbidden`

The response is a genuine served response from the **proven guarded pipeline**, not
a parse fallback. `serveOverSubs` reaches `guardOnSubs` (and thus the `403`) only
when `Reactor.Deploy.dispatchReqOf subs = some req` — i.e. only when a dispatched
H3 request exists. The decoded `GET /` therefore reached the dispatch and the real
`Reactor.Deploy` Policy gate, which returns `policy: undeclared surface` for a bare
`/` with no declared route. Decrypt → H3 decode → dispatch → guarded serve →
response is the whole chain, end to end, over the socket.

## Reproduce

```sh
cd <repo>
./ffi/build-crypto-shim.sh          # ffi/crypto_shim.o (HACL*/EverCrypt)
./ffi/build-mac-multi.sh            # ffi/mac_udp.o (the untrusted UDP shell)
~/.elan/bin/lake build orb-quic
./.lake/build/bin/orb-quic 8443 &   # self-test runs, then binds the socket
python3 <scratchpad>/quic_client.py 8443
```

## Scope — what a real `quiche` / `curl --http3` handshake still needs

The server decrypts a real/crafted Initial packet over the socket via verified
EverCrypt and reaches the proven H3 dispatch. A full off-the-shelf QUIC client
handshake additionally requires, none of which is faked here:

1. **Header protection** (RFC 9001 §5.4). A real Initial masks the first byte's low
   bits and the packet number with a mask derived from a ChaCha20 (or AES-ECB)
   *sample* of the ciphertext. The `Crypto` seam exposes only AEAD (ChaCha20-Poly1305
   / AES-GCM), not a raw ChaCha20 block or AES-ECB, so HP removal needs a new
   verified primitive. The crafted packet here carries the first byte + packet
   number in the clear (still the RFC 9000 wire layout, minus the HP masking step).
2. **AES-128-GCM for the Initial** (RFC 9001 §5.2). A real client's Initial is
   AES-128-GCM, not ChaCha20-Poly1305. `Crypto` has AES-GCM at a 256-bit key; the
   Initial needs a 16-byte-key AES-128-GCM primitive (`deriveChachaKeys` →
   `deriveAes128Keys`, key length 16).
3. **CRYPTO frame + TLS ClientHello**. A real Initial carries a CRYPTO frame with
   the TLS 1.3 ClientHello, not an H3 HEADERS stream. Wiring `TlsHandshake` behind
   the QUIC CRYPTO-frame reassembler would produce the server's
   ServerHello/EncryptedExtensions/Certificate/Finished in the server Initial +
   Handshake packets.
4. **The Initial → Handshake → 1-RTT key transition** (RFC 9001 §4, §7). H3 requests
   arrive only in 1-RTT packets after the handshake installs application keys.
   `QuicTransport.KeyState` models this monotone install discipline (proved:
   `quic_no_1rtt_before_handshake`) but it is not driven from the socket here; the
   decrypted Initial STREAM frame is fed to the established-connection H3 dispatch
   (`demoState`) rather than run through the live handshake FSM.
5. **Packet-number decoding** (RFC 9000 §17.1 / App. A) — truncated-PN
   reconstruction against the largest acked packet number.
6. **The rest of the transport** — Retry, version negotiation, ACK/flow-control
   frames, transport parameters, connection-ID negotiation, and short-header
   (1-RTT) packet parsing for the actual request/response exchange.

What is real and observed here: a datagram off a real UDP socket, its protected
payload opened by the F\*-verified EverCrypt ChaCha20-Poly1305 at RFC 9001 keys and
nonce (with the authenticity gate demonstrated to reject a forgery), then dispatched
by the unchanged proven H3 ingress.
