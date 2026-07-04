# QUIC-INGRESS — HTTP/3 over QUIC is runtime-reachable (kernel-executed)

`Reactor/QuicIngress.lean` adds the HTTP/3-over-QUIC datagram path to the running
reactor. Without this file the runtime speaks HTTP/1.1 and h2c prior-knowledge
(`Reactor.Ingress` forks the TCP listener on the first bytes). The QUIC and
HTTP/3 libraries were real and proven — `Quic.step` (the connection FSM,
RFC 9000), `H3.decFrame` (the frame decoder, RFC 9114), and
`H3.Qpack.decodeFieldSection` (QPACK-into-arena, RFC 9204) — and `Reactor.Quic`
had already wired them onto one datagram (`Reactor.Quic.step`, `quic_drives_h3`).
But that path stopped at a decoded `StreamOut`; it never crossed into the
reactor's dispatch vocabulary (`RingSubmission.dispatch`), so no H3 request could
reach the deployed serve — without this file the QUIC engine is
decoded but never dispatched on the running binary.

This file is the QUIC analogue of `Reactor.H2Ingress` (which does the same for
h2c). It carries a decoded QPACK head all the way to a dispatched
`Proto.Request`, so an HTTP/3 request enters the *same* `RingSubmission` pipeline
the H1/h2c paths feed.

## What runs

`datagramServe` is the datagram-lane serve entry — the QUIC sibling of
`Reactor.Ingress.deployStepIngress`. Given the path state and one datagram event,
it runs the REAL `Reactor.Quic.step` (real `Quic.step` + real `H3.decFrame` +
real `H3.Qpack.decodeFieldSection`) and returns the advanced path state together
with the reactor `RingSubmission`s the deployed serve consumes — chiefly the
`dispatch` of the H3-decoded request.

`requestOfHeaders` is the QPACK-head → `Proto.Request` bridge, the sibling of
`Reactor.H2.requestOfDecoded`: the `:method`/`:path` pseudo-headers (resolved
back to bytes through the REAL `Arena.Store.resolve` against the store the QPACK
decode grew) fill the request line, the QPACK field lines fill the header list,
and the version is the fixed HTTP/3 marker.

## The runtime execution proof (kernel `#guard`)

The `#guard demoDispatchesGet` in the file kernel-evaluates the whole real path.
It drives `datagramServe` on an app-data QUIC datagram carrying a concrete
on-wire H3 HEADERS frame:

```text
01            frame type = 0x01 (HEADERS)
04            length     = 4
00 00         QPACK section prefix (Required Insert Count 0, Delta Base 0)
d1            indexed static line 17 (:method: GET)
c1            indexed static line 1  (:path: /)
```

into an established connection, and checks the dispatched request's resolved
method is `GET`, target is `/`, version is `HTTP/3`. This forces evaluation of
`Reactor.Quic.step → Quic.step` (delivery) `→ H3.decFrame → H3.Qpack.decodeFieldSection
→ Arena.Store.resolve` — the real engines, run on a real input. It is an
execution, not a description. A second `#guard` pins that the lane emits exactly
one submission, and that it is a `dispatch`.

## The seam theorem — `quic_ingress_dispatch`

A well-formed H3 HEADERS datagram in the app-data space, into an *established*
connection, whose stream carries a decodable HEADERS frame whose QPACK field
section decodes to `d`, makes `datagramServe` emit **exactly**

```text
[ RingSubmission.dispatch (requestOfHeaders d.store d.pseudo d.fields) ]
```

The equality is of `datagramServe`'s own output — not a correspondence beside an
unchanged pipeline. It is proven by carrying `Reactor.Quic.quic_drives_h3` (the
transport composition: the real QUIC delivery gates the H3 decode via
`Quic.no_appdata_before_established`, and the arena stays well-formed via
`H3.Qpack.decodeFieldSection_wf`) through the ingress into the reactor's dispatch
vocabulary. The dispatched request's method/target are *meaning*, resolved from
the real decoded arena entries — not a bound or a totality claim.

## Verification

* Single-file check: `lake env lean Reactor/QuicIngress.lean`
* Module target: `lake build Reactor.QuicIngress` (builds clean)
* Zero `sorry`. `#print axioms quic_ingress_dispatch` reports
  `[propext, Classical.choice, Quot.sound]` — the standard classical core only,
  no extra axioms.

## What still defaults to TCP

The shipped orb exe still DEFAULTS to TCP: `Arena.Orb.main` and the native IO
drivers (`orb-mac` / `orb-linux` / `orb-win`) run `deployStepIngress` over a byte
stream. This file makes the QUIC/H3 path **runtime-reachable and kernel-executed**
and exposes `datagramServe` as the entry a UDP socket driver
selects: recv a datagram, call `datagramServe`, feed the emitted `dispatch` into
the same guarded serve the TCP path runs. The UDP socket driver (the analogue of
`ffi/*_io.c` for datagrams) is the remaining wiring; the proven core it will run
is in place and executes today.
