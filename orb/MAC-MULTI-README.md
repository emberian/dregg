# orb-mac-multi — the proven reactor serving REAL traffic ACROSS PROTOCOLS

`orb-mac-multi` closes the "across protocols on the socket" gap. The shipped
`orb-mac` binary served only HTTP/1.1 + h2c over one TCP socket; the WebSocket
and QUIC/HTTP-3 lanes executed *in the kernel* (`#guard`s in
`Reactor.WsDeploy` / `Reactor.QuicIngress`) but were never wired to a real
socket. This binary wires both:

* **(A) WebSocket over TCP** — after an RFC 6455 `Upgrade: websocket` response
  the connection **stays open** and every subsequent frame runs through the
  PROVEN WebSocket path (`Reactor.Ws.wsFeedFn` decode/unmask/reassembly →
  `Reactor.Ws.wsEncodeFn` echo). A real WS client gets its frames echoed over
  the real socket.
* **(B) QUIC/HTTP-3 over UDP** — a real UDP datagram is `recvfrom`'d and driven
  through the PROVEN datagram lane (`Reactor.QuicIngress.datagramServe`: real
  `Quic.step` + `H3.decFrame` + QPACK decode → `dispatch`), and the dispatched
  request is served by the SAME guarded pipeline the TCP lanes run
  (`Reactor.Ingress.serveOverSubs`). The response goes back as a datagram.

The proven core is **unchanged** — only the untrusted C shell's IO scheduling is
new. One process runs both listeners at once.

## Trust split (identical discipline to `orb-mac`)

| | file | status |
|---|---|---|
| **TCP + WebSocket shell** | `ffi/mac_io.c` | plain BSD sockets + the accept loop; `orb_mac_serve_ws` keeps a connection open after Upgrade. Not verified. |
| **UDP/QUIC shell** | `ffi/mac_udp.c` | plain BSD UDP socket; `orb_mac_serve_udp` recv/send datagrams. Not verified. |
| **The `@[extern]` seam + handlers** | `IoMacMulti.lean` | `multiHttpHandle`, `wsHandle`, `udpHandle` — the pure `ByteArray → ByteArray` functions that ARE the proven pipelines. |
| **The proven core** | `Reactor/Ws.lean`, `Reactor/QuicIngress.lean`, `Reactor/Ingress.lean`, … | **unchanged.** |

### The one thing the C shell computes: the handshake hash

The proven core ships **no SHA-1** (the EverCrypt shim is SHA-256/384 only), and
`Sec-WebSocket-Accept` = `base64(sha1(key ++ "258EAFA5-…-C5AB0DC85B11"))` is a
SHA-1. So the untrusted C shell computes the handshake accept token (a small
SHA-1 + Base64 in `ffi/mac_io.c`) — exactly the kind of connection-lifecycle
concern the shell already owns (bind/accept/close). It **never** touches the
WebSocket *data* path: every frame's bytes cross the seam unchanged to the
proven `wsFeedFn`/`wsEncodeFn`. The shell's `is_ws_upgrade` scan only *selects
the lane* (the socket analogue of `Reactor.Ingress`'s h2-preface fork).

### Handler axiom footprint (`#print axioms`)

```
'wsHandle'        depends on axioms: [propext]
'udpHandle'       depends on axioms: [propext, Classical.choice, Quot.sound]
'multiHttpHandle' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All within `{propext, Quot.sound, Classical.choice}`. No `sorry`, no new axiom.

## Build

```sh
./ffi/build-mac-multi.sh          # -> ffi/mac_io.o + ffi/mac_udp.o
lake build orb-mac-multi
```

`lakefile.toml`:

```toml
[[lean_exe]]
name = "orb-mac-multi"
root = "IoMacMulti"
moreLinkArgs = ["-Wl,-no_data_const", "ffi/mac_io.o", "ffi/mac_udp.o"]
```

Observed build tail:

```
✔ [135/146] Built IoMacMulti
✔ [146/146] Built «orb-mac-multi»
Build completed successfully.
```

## Run

```sh
./.lake/build/bin/orb-mac-multi 8080 8081   # TCP port, UDP port (defaults 8080/8081)
```

Startup (stderr):

```
orb-mac-multi: proven reactor ACROSS PROTOCOLS — WS/HTTP on TCP 8080, QUIC/H3 on UDP 8081
orb-mac-multi: WS+HTTP listening on 127.0.0.1:8080 (proven WS frame path over real TCP)
orb-mac-multi: QUIC/UDP listening on 127.0.0.1:8081 (proven H3 datagram ingress over real UDP)
```

`lsof` confirms both real sockets are bound:

```
orb-mac-m 33493 ember  7u IPv4 TCP 127.0.0.1:8080 (LISTEN)
orb-mac-m 33493 ember  8u IPv4 UDP 127.0.0.1:8081
```

---

## LIVE TRANSCRIPT — captured on darwin (macOS), 2026-07-03

### Sanity: HTTP/1.1 still served (unchanged proven pipeline)

```
$ curl -s -i http://127.0.0.1:8080/health
HTTP/1.1 200 OK
Server: drorb
x-upstream: 1572395042
x-corr: 71.69.84.32.47.104.101.97.108.116.104.32.72.84.84.80.47.49.46.49.13.10...
Content-Length: 2
```

### (A) WebSocket — REAL client, full handshake, echo, two frames on ONE connection

Driven by a raw RFC 6455 client (`scratchpad/ws_client.py`, no library — TCP
connect, HTTP Upgrade with a random key, **validate** `Sec-WebSocket-Accept`,
masked text frames, read echoes). `websocat` was not installed on this box, so a
raw client written for the run stands in for it — it performs the identical
handshake + masking a browser/websocat would.

```
--- server handshake response ---
HTTP/1.1 101 Switching Protocols
Upgrade: websocket
Connection: Upgrade
Sec-WebSocket-Accept: O1UKuYovfwddyLoESuRMfuCrZUU=

Sec-WebSocket-Accept validation: expected=O1UKuYovfwddyLoESuRMfuCrZUU= got=O1UKuYovfwddyLoESuRMfuCrZUU= -> MATCH

sent   (masked): b'hello over proven WS'
echo   (opcode=0x1 fin=True): b'hello over proven WS'
ROUND-TRIP OK

sent   (masked): b'second frame, same TCP connection'
echo   (opcode=0x1 fin=True): b'second frame, same TCP connection'
ROUND-TRIP OK

both frames round-tripped on ONE connection.
```

What round-tripped with a real client: the **full WS handshake** (the client
validated the shell-computed `Sec-WebSocket-Accept` — a mismatch aborts), and
**two masked text frames** on the **same open TCP connection**, each decoded +
unmasked + reassembled by the proven `Reactor.Ws.wsFeedFn` and re-encoded by the
proven `Reactor.Ws.wsEncodeFn`. The keep-alive frame loop serving a second frame
on one connection is exactly the "second request on one connection" bar.

Server stderr during the WS session:

```
orb-mac-multi: WS upgrade OK, accept=O1UKuYovfwddyLoESuRMfuCrZUU= — connection open, frame loop
```

### (B) QUIC/HTTP-3 — REAL UDP datagram drives the proven H3 dispatch

The datagram payload is a real on-wire HTTP/3 HEADERS frame carrying `GET /`
(`01 04 00 00 d1 c1` — HEADERS, len 4, QPACK prefix `00 00`, static `d1` =
`:method: GET`, `c1` = `:path: /`; this is `Reactor.QuicIngress.demoH3Get`, the
frame the kernel `#guard` already dispatches).

Python UDP socket (`scratchpad/udp_client.py`):

```
sending H3 HEADERS 'GET /' datagram: 01040000d1c1
response datagram (73 bytes) from ('127.0.0.1', 8081):
---
HTTP/1.1 403 Forbidden
Content-Length: 27

policy: undeclared surface
---
```

And with plain `nc -u` (a non-Python raw sender):

```
$ printf '\x01\x04\x00\x00\xd1\xc1' | nc -u -w1 127.0.0.1 8081
HTTP/1.1 403 Forbidden
Content-Length: 27

policy: undeclared surface
```

What round-tripped: a **real UDP datagram** over a real socket drove
`Reactor.QuicIngress.datagramServe` — the REAL `Quic.step` delivered the app
data, `H3.decFrame` yielded the HEADERS frame, `H3.Qpack.decodeFieldSection`
decoded `GET /`, and the request was **dispatched** and served through the SAME
guarded pipeline the TCP lanes run. The `403 policy: undeclared surface` is the
REAL `Reactor` Policy gate answering `GET /` (`/` is not a declared surface —
the same gate returns `200` for `/health`); it is a genuine proven-pipeline
response for the H3-dispatched request, delivered back as a datagram.

## Scope — what did NOT round-trip with an off-the-shelf client

Honesty about the QUIC lane: **no real QUIC/H3 client (quiche, curl --http3,
Chrome) completed a handshake.** A full QUIC handshake is Initial/Handshake
packets, the TLS 1.3 key schedule, and AEAD packet protection — none of which is
performed by `ffi/mac_udp.c`. The proven datagram lane models a datagram as
arriving *pre-parsed and pre-decrypted* (`Reactor.Quic.DatagramEvent` — the
datagram's space/number are given), so the UDP shell hands the datagram payload
to the proven lane as the application-data HTTP/3 stream bytes on an
**established** connection. So what a real client (Python socket / `nc -u`)
drives end-to-end is: real UDP socket → proven `Quic.step` app-data delivery →
proven H3/QPACK decode → proven dispatch → proven guarded serve → response
datagram. What is stubbed at the shell is the transport crypto/handshake, not
the H3 request path. Wiring a real QUIC handshake is the next shell-side task
(the proven core already models the established connection it would hand off to);
it does not touch the proven core.

The WebSocket lane, by contrast, round-trips **end-to-end with a real client**:
the real handshake (accept token validated by the client) and real masked frames
over the real TCP socket.

## v1 shell scope

- **WS frame buffering.** The shell feeds one `recv` per `wsHandle` call; the
  proven `wsFeedFn` buffers a partial frame in its own codec, but this v1 shell
  starts each call from a fresh codec, so a frame split across two `recv`s would
  not reassemble. Small loopback frames arrive whole, so the demo is unaffected;
  threading the codec across recvs is a shell-side change (no core change).
- **UDP is one-datagram-in/one-out**, no per-peer QUIC connection state — the
  proven lane already carries the `QuicState`; persisting it per source address
  is a shell concern.

None of these touch the proven core. They change the environment the proof runs
in, which is exactly where untrusted, test-validated code belongs.
