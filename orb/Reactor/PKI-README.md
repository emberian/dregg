# Reactor.Pki — the PKI accept gate wired into the running TLS handshake

`Reactor/Pki.lean` wires two real PKI libraries — **Resume** (session-resumption
tickets + OCSP staple freshness) and **Mtls** (client-certificate chain
validation) — into the one place the TLS handshake *accepts* a connection, on the
path the reactor actually runs.

## Where it plugs in

`Reactor.Tls` already drove the real `Tls` handshake machine through the FSM's
opaque `TlsConn` handle: `TlsWire.hsFeedReal tcfg` turns the handshake engine's
phase into the FSM's `HsOut` (`.more` while handshaking, `.done` on completion,
`.fail` on teardown), and `wireTls` installs it into `Config.hsFeed`.

`Config.hsFeed` is the function the running reactor calls on every
`.tlsHandshake` byte:

```
Proto.step  →  Proto.onBytes (… .tlsHandshake tc tlsBuf …)  →  Proto.hsStep  →  cfg.hsFeed tc buf
```

`Reactor.Pki` interposes on exactly that field. `pkiHsFeed base pcfg` runs the
underlying handshake (`base = hsFeedReal tcfg`) unchanged and, **only** on the
accept (`.done`), applies the PKI gate `pkiOk`. A refused accept is turned into
`.fail`; `.more`/`.fail` pass through untouched. `wirePki tcfg pcfg cfg` installs
`pkiHsFeed (hsFeedReal tcfg) pcfg` into `Config.hsFeed`, so the gate is invoked
by the running FSM — not a handler left dangling off to one side.

`wiredPkiConfig tcfg pcfg` is the concrete reactor config with the real TLS
engine and the PKI gate both plugged in over the arena-backed HTTP/1.1
`demoConfig` (its `tlsRecv`/`tlsSend` remain the real record adapters —
`wiredPkiConfig_tlsRecv`).

## The three gates, each a call into a real library

`PkiCfg` carries the check time, the ticket key epoch, an optional stapled OCSP
response, the mTLS verification context (`Mtls.Env`: the named signature
interface + trust anchors), a required-mTLS flag, and two total presentation
functions that surface the client-presented credentials out of the handshake
handle/buffer (`ticketOf`, `chainOf`). Every function-valued field is total, so
the theorems hold uniformly over every presentation behaviour — the same named
boundary shape `Tls.Config` uses for the crypto.

* `resumeOk` — no ticket ⇒ full handshake, passes; a ticket ⇒ the real
  `Resume.accept` decides it against the validity window and key epoch.
* `ocspOk` — no staple ⇒ passes; a staple ⇒ the real `Resume.Staple.fresh`
  refuses a stale one.
* `mtlsOk` — mTLS required ⇒ the real `Mtls.authenticate` must have derived an
  identity (i.e. the chain validated); otherwise passes.

`pkiOk = resumeOk && ocspOk && mtlsOk`, and `pkiHsFeed` accepts only when it
holds (`pkiHsFeed_done_pkiOk`).

## The seam theorems

Decision-level (composing with the TLS accept):

* **`pki_resume_window`** — if a session ticket is presented and the wired
  handshake accepts (`.done`), then `now` lies inside the ticket's half-open
  validity window `[issued, expiry)`. This is the real `Resume.accept_in_window`
  transported through the accept: the accept fired only because `resumeOk` held,
  and with a ticket present `resumeOk` *is* `Resume.accept`.
* **`mtls_no_auth_on_failure`** — with mTLS required, a chain that fails the real
  `Mtls.verifyFrom` never lets the wired handshake reach `.done`; no
  authenticated session is established on a failed chain. Composes
  `Mtls.authenticate_unverified` (a failed chain yields no identity) with the
  accept gate. `mtls_identity_verified` further shows any derived identity comes
  only from a validated chain (`Mtls.authenticate_eq_some`).
* **`pki_ocsp_fresh`** — if the wired handshake accepts while a staple is
  configured, that staple was fresh (`now < nextUpdate`) per `Resume.fresh_iff`.

Reactor-level (composing with the running `Proto.onBytes`):

* **`mtls_no_auth_on_failure_reactor`** — on the running path, an mTLS handshake
  whose presented chain fails validation never reaches an established protocol
  state: `Proto.onBytes` on the `.tlsHandshake` state either closes the
  connection or leaves it still handshaking.
* **`pki_resume_window_reactor`** — a ticket presented outside its validity
  window can likewise never carry the connection into an established protocol
  state.

Both reactor forms go through the shared lemma `hsStep_no_done`: `Proto.hsStep`
enters `runH1`/`runH2` (an established state) *only* on `.done`, so a gate that
never accepts keeps the FSM in `.tlsHandshake` or closes it.

## Verification status

`lean Reactor/Pki.lean` typechecks green against the current build oleans; zero
sorries. `#print axioms` on all six seam theorems reports `[propext]` only —
within the allowed `{propext, Quot.sound, Classical.choice}` subset.

Scope: `Reactor/Pki.lean` and `Reactor/PKI-README.md`, plus
the `import Reactor.Pki` line in `Reactor.lean`. Nothing in the shared spine
(`Proto/Basic.lean`, `Reactor/Config.lean`) was touched.
