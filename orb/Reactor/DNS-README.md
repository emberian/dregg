# DNS-WIRE — resolve an upstream hostname with the real DNS parser before connecting

`Reactor/Dns.lean` (namespace `Reactor.DnsWire`) wires the real `Dns` library into the
reactor's upstream-connect path. Before the reactor honors a connect to an upstream, the
target hostname is resolved by driving the real RFC 1035 message parser — header,
question, and resource-record parse, with the anti-loop name decompression — to an
address.

## What runs

The reactor already emits `RingSubmission.connectUpstream addr` on two real paths:

  * the FSM's SOCKS/tunnel `Proto.Output.connectUpstream`, translated by
    `Reactor.Contract.ofOutput` (the running `Reactor.step`); and
  * the reverse-proxy handler `Reactor.Proxy.proxyHandle`, which asks to connect to the
    backend the real load-balancer chose.

`resolveSubs` sits on that stream. For every `connectUpstream a` it drives the real DNS
resolution of `a`'s hostname and rewrites the submission to a connect to the *resolved*
address — or drops it when the host has no answer. Every other submission passes through
untouched (so the copy-once buffer recycle, sends, dispatches are all preserved).

## The resolution — real `Dns` code, not a stub

`resolve host msg` (`Reactor/Dns.lean`) calls:

  * `Dns.parseHeader` — requires `ANCOUNT ≥ 1`;
  * `Dns.parseQuestion` — parses the question name (via `Dns.decodeName`) and checks it
    matches the queried `host`;
  * `Dns.parseRR` — parses the first answer record (its NAME again via `Dns.decodeName`)
    and, on an `A` record (type 1), reads the 4-octet RDATA as the `Proto.Addr`
    (`Dns.be32`).

`Dns.decodeName` is where the **anti-loop termination guarantee** lives: a compression
pointer is followed only when it jumps strictly backward, so no adversarial pointer
arrangement can diverge. `resolve` inherits this: `resolve_total` states it returns a
value on every `(host, msg)`, loops included, and `dns_terminates_on_loop` exhibits a
self-pointer answer name (`C0 14`) that the real decoder rejects as `loopPointer` — so the
reactor issues no connect rather than hanging.

## The seam theorem — `dns_resolves_before_connect`

> Every `connectUpstream a'` surviving the pass carries an `a'` that is the real
> `Dns.resolve` of the response bytes the resolver held for some pre-resolution connect
> `a` the reactor actually emitted: `∃ a host msg, connectUpstream a ∈ subs ∧ R.lookup a =
> some (host, msg) ∧ resolve host msg = some a'`.

So the address the reactor dials is *derived from a real DNS parse of the backend
hostname*, never a hardcoded target, and never a host that failed to resolve (the
`resolve host msg = some a'` conjunct). A stubbed resolver whose output did not equal
`Dns.resolve msg` would fail that conjunct.

Companion facts:

  * `unresolved_dropped` — a connect whose host does not resolve is removed from the
    stream (no connect to an unresolved host).
  * `resolved_forwarded` — a resolved connect is forwarded to the DNS-derived address.
  * `resolve_msgUp` — the real parser reads `93.184.216.34` (be32 `1572395042`) from a
    concrete response; a stub could not produce that value.

## Wired on a path that runs

  * `dns_wired_running` — drives the *real* `Reactor.step` on a SOCKS connection
    (`dnsSocksConfig`), which emits a genuine `connectUpstream ⟨7⟩` (marker) plus the
    copy-once recycle; after the pass the reactor targets the DNS-parsed address
    `⟨1572395042⟩` and the recycle is untouched.
  * `dns_wired_proxy` — over the real `Reactor.Proxy.proxyHandle` output: the proxy picks
    backend `demoB2` (address `⟨2⟩`); the pass resolves that host and the reactor targets
    the DNS-parsed address. This is "resolve before connect" sitting exactly between the
    proxy's `Addr` and the actual connect.

## Ownership / build

  * Owns `Reactor/Dns.lean` (new) and its import line in `Reactor.lean`.
  * `lake build Reactor` is green; zero sorries.
  * `#print axioms` for the seam theorems ⊆ `{propext, Quot.sound, Classical.choice}`.

## Not yet / follow-ups

  * The pre-resolution `Proto.Addr.id` is used as an opaque host handle keyed by the
    `Resolver`; a richer wiring would carry the hostname bytes on the connect submission
    itself so the resolver needs no side table.
  * The `Resolver` supplies response bytes directly (a cache/stub transport); a live query
    round-trip (emit a DNS request submission, resolve on its completion) is a later slice.
  * `resolve` reads only the first `A` answer; AAAA/CNAME-chase and multi-record selection
    are widenings that keep `resolve` as their base case.
