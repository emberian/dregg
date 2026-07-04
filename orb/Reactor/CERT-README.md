# CERT — the real Acme issuance FSM and the real Ct Merkle log, wired into the TLS cert path

`Reactor/Cert.lean` (namespace `Reactor.CertWire`).

## What is wired

Two real libraries now condition the TLS accept on the deployed path:

* **Acme** (`Acme.Order`, `Acme.Challenge`) — the issuance step. An
  `Issuance` is a run of the real RFC 8555 order FSM (`Acme.orderRun` over
  `Acme.Order.fresh`). The certificate is available to the TLS accept path
  (`acmeCert = some certData`) **only** when that run has reached
  `OrderStatus.valid` — the status at which the CA issues. Every other status
  yields `none`; there is no second constructor.

* **Ct** (`Ct.Inclusion`) — the SCT check. The server carries `Sct` evidence
  (index, tree size, audit path, signed tree head) and the gate runs the real
  RFC 6962 verifier `Ct.verifyInclusion` on `hleaf certData` against that
  head. Literally the library function, no adapter arithmetic.

`certOk = (acmeCert = some cert) && sctVerified` gates the handshake accept
through the same `PkiWire.gateDone` the PKI lane uses: only `.done` is gated,
a refused accept becomes `.fail`, `.more`/`.fail` pass through.

## The deployed path

`wireCert ccfg cfg` composes over the feeder a config already carries.
The deployed instantiation is

```
wiredCertConfig tcfg pcfg ccfg
  = wireCert ccfg (PkiWire.wiredPkiConfig tcfg pcfg)
  = cert gate ∘ PKI gate ∘ TlsWire.hsFeedReal tcfg   -- over demoConfig
```

i.e. cert gate over PKI gate over the real `Tls.step` handshake adapter over
the arena-backed `Reactor.Config.demoConfig` the orb serves. No-drift
theorems pin this: `wiredCertConfig_hsFeed` (the feeder is exactly the
stacked gates over `hsFeedReal`, `rfl`), `wiredCertConfig_tlsRecv` (record
layer still real), `wiredCertConfig_h1Parse` (arena parser still
`h1ParseFn`). The running reactor invokes the gated feeder on every
`.tlsHandshake` byte: `Proto.onBytes → Proto.hsStep → cfg.hsFeed`.

## Seam theorems (all `lake`-checked, axioms ⊆ {propext, Quot.sound, Classical.choice})

* **`acme_issues_before_serve`** — if the deployed `hsFeed` accepts
  (`.done`), then `acmeCert ccfg = some certData`, the real order run is at
  `valid`, and — composing the Acme library's inductive invariant
  `valid_requires_all_authz_valid` — **every authorization of that order is
  valid**. A cert is used only after the real Acme order reaches `valid`.

* **`acme_no_challenge_bypass`** — pushed through the Acme
  challenge→authorization bridge (`authzOfChalStatus`, via the pointwise
  lemma `allValid_bridge`): a deployed accept forces every discharging
  challenge to be `valid`; the Acme library proves the only door into a valid
  challenge is a successful validation (`chal_into_valid`,
  `validateStep_valid_needs_success`).

* **`ct_inclusion_seam`** — a deployed accept implies
  `Ct.verifyInclusion hs (hleaf certData) index size path root = true`: the
  cert is accepted only if the real Ct inclusion proof verifies.

* **`ct_cert_logged`** — composed with the library's collision-resistance
  soundness (`Ct.inclusion_sound`, surfaced as `sctVerified_sound` for
  arbitrary/adversarial paths): against the genuine head of the real log,
  an accepted cert **is** the genuine `index`-th logged leaf.

* Reactor forms: **`acme_gate_reactor`** (order not `valid` ⇒ `Proto.onBytes`
  on the deployed wired config closes or stays in handshake — issuance
  strictly precedes serving) and **`ct_gate_reactor`** (failing inclusion
  proof ⇒ same). Both reuse `PkiWire.hsStep_no_done`.

* **`wiredCert_accept`** — the full-stack accept: one `.done` on the deployed
  feeder discharges `certOk` **and** the PKI gate (`pkiOk`) underneath
  (`gateDone_done_base` shows the gate never rewrites an accept's payload).

* Liveness sanity (the gate is not vacuously closed):
  **`demoIssuance_valid`** — the honest trace `[authzResult 0 true, finalize,
  issued]` really drives the order FSM to `valid` (`rfl`);
  **`honestSct_verifies`** — the real `Ct.auditPath` over the real log
  verifies (`Ct.inclusion_iff` ←); **`certOk_satisfiable`** — together they
  open the composite gate.

## Shape notes

* `certData` is one object: the same value the Acme availability gates and
  the Ct verifier hashes — the two checks cannot diverge onto different
  certificates.
* The hash is the Ct library's abstract `HashScheme` (collision resistance +
  domain separation as structure fields, not Lean axioms), so the axiom
  footprint stays core-only.
* `Reactor.lean` gained `import Reactor.Cert`.
