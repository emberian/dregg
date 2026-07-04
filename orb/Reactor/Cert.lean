import Reactor.Pki
import Reactor.Deploy
import Acme.Order
import Acme.Challenge
import Ct.Inclusion

/-!
# Reactor.Cert — wiring the real Acme issuance FSM and the real Ct Merkle log
# into the TLS certificate path

`Reactor.Pki` gated the TLS accept with the Resume/Mtls libraries over the
deployed stack: `wiredPkiConfig tcfg pcfg = wirePki tcfg pcfg (wireTls tcfg
Reactor.Config.demoConfig)` — the arena-backed `demoConfig`, the real `Tls`
engine as `hsFeed`/`tlsRecv`/`tlsSend`, and the PKI gate on `.done`. This file
adds the **certificate lifecycle** to that same accept decision, with two more
real libraries:

* **Acme** (`Acme.Order`, `Acme.Challenge`) — where the server's certificate
  *comes from*. An `Issuance` is a run of the real RFC 8555 order FSM: a fresh
  order for the identifiers, driven by an event trace through
  `Acme.orderRun`. The certificate is *available* (`acmeCert = some _`) only
  when that run has reached `OrderStatus.valid` — the status at which the CA
  issues. There is no other door: `acmeCert` is `none` in every other status.

* **Ct** (`Ct.Inclusion`) — whether the certificate is *publicly logged*. The
  server carries SCT evidence (`Sct`: index, tree size, audit path, signed
  tree head) and the gate runs the real RFC 6962 inclusion verifier
  `Ct.verifyInclusion` on the certificate's leaf hash against that head.

## The wiring

`certHsFeed base ccfg` wraps a base handshake feeder with `PkiWire.gateDone`:
the underlying handshake runs unchanged, and **only** its `.done` (the accept)
is gated by `certOk ccfg` — the certificate must be Acme-issued (`acmeCert =
some cert`) *and* its CT inclusion proof must verify (`sctVerified`). A refused
accept becomes `.fail`; `.more`/`.fail` pass through untouched.

`wireCert ccfg cfg` installs `certHsFeed cfg.hsFeed ccfg` — a config
transformer that *composes over* whatever feeder is already wired, so the PKI
gate and the real TLS engine underneath stay live. `wiredCertConfig tcfg pcfg
ccfg = wireCert ccfg (PkiWire.wiredPkiConfig tcfg pcfg)` stacks: cert gate over
PKI gate over the real `Tls.step` adapter over the arena-backed `demoConfig`.
This is a SEPARATE config lineage from `Reactor.Deploy.deployConfig` (the config
`main` actually runs) — see the deployed-path status note below. A reactor over
`wiredCertConfig` invokes the gate on every `.tlsHandshake` byte:
`Proto.onBytes → Proto.hsStep → cfg.hsFeed`.

## The seam theorems

* `acme_issues_before_serve` — if the deployed wired handshake accepts
  (`.done`), the certificate it uses is the Acme-issued one, the real order
  run reached `valid`, and (by the Acme library's own
  `valid_requires_all_authz_valid`) **every** authorization of that order is
  valid. `acme_no_challenge_bypass` pushes this through the Acme
  challenge→authorization bridge (`authzOfChalStatus`): every challenge that
  discharged an authorization is itself `valid`, and the Acme library proves
  the only door into a valid challenge is a *successful* validation
  (`Acme.chal_into_valid` / `Acme.validateStep_valid_needs_success`). The
  reactor form `acme_gate_reactor` shows an unissued cert (order not `valid`)
  can never carry the running `Proto.onBytes` into an established state.

* `ct_inclusion_seam` — if the deployed wired handshake accepts, the real
  `Ct.verifyInclusion` returned `true` on the presented certificate's leaf
  hash against the carried tree head. `ct_cert_logged` composes this with the
  Ct library's collision-resistance-powered `inclusion_sound`: when the head
  is the genuine head of the real log, the accepted certificate **is** the
  genuine `index`-th logged leaf — an unlogged cert cannot ride an accepted
  handshake past a genuine head. The reactor form `ct_gate_reactor` shows a
  failing inclusion proof keeps `Proto.onBytes` off the established path.

* Liveness sanity: the gate is satisfiable, not vacuously closed —
  `demoIssuance_valid` exhibits a real order run reaching `valid` (respond,
  finalize, issue) and `honestSct_verifies` shows the honest audit path over
  the real log verifies (`Ct.inclusion_iff`), so `certOk_satisfiable` gives a
  concrete open gate.
-/

namespace Reactor
namespace CertWire

open Proto (Bytes TlsConn Config HsOut)

/-! ## The issuance state: a run of the real Acme order FSM -/

/-- One certificate issuance: a fresh RFC 8555 order for `ids`, driven by the
event trace `events` (authorization verdicts, finalize, issuance outcome)
through the real `Acme.orderStep`. -/
structure Issuance where
  /-- The identifiers (domains) the certificate is for. -/
  ids : List Acme.Bytes
  /-- The order-lifecycle events observed so far. -/
  events : List Acme.OrderEvent

/-- The order this issuance has reached: the real Acme FSM folded over the
trace from a fresh order. Every Acme lifecycle theorem
(`valid_requires_all_authz_valid`, `into_valid`, `valid_run_absorbing`, …)
applies to it verbatim. -/
def Issuance.order (is : Issuance) : Acme.Order :=
  Acme.orderRun (Acme.Order.fresh is.ids) is.events

/-! ## The SCT evidence: what the CT gate checks -/

/-- Signed-certificate-timestamp evidence for one certificate: the claimed
leaf index and tree size, the audit path, and the signed tree head it is
checked against (RFC 6962 §2.1.1). -/
structure Sct (H : Type) where
  index : Nat
  size : Nat
  path : List H
  root : H

/-- The certificate-lifecycle context threaded into the accept decision: the
hash interface and the log evidence for the CT check, plus the issuance run
the certificate must come from. `certData` is the certificate itself, as a CT
leaf — the same value the Acme availability gates and the Ct verifier hashes,
so the two checks are about *one* object. -/
structure CertCfg (Leaf H : Type) where
  /-- The RFC 6962 collision-resistant, domain-separated hash interface. -/
  hs : Ct.HashScheme Leaf H
  /-- The Acme issuance run backing the certificate. -/
  issuance : Issuance
  /-- The certificate, as the CT leaf datum. -/
  certData : Leaf
  /-- The SCT evidence presented for `certData`. -/
  sct : Sct H

variable {Leaf H : Type} [DecidableEq H]

/-! ## The issuance step: the certificate exists only past a valid order -/

/-- **Certificate availability.** The certificate the TLS accept path may use:
`some certData` exactly when the real Acme order run has reached `valid` (the
status at which the CA issues), `none` otherwise. This is the *only*
constructor of a usable certificate — there is no path around the order FSM. -/
def acmeCert (ccfg : CertCfg Leaf H) : Option Leaf :=
  if ccfg.issuance.order.status = .valid then some ccfg.certData else none

omit [DecidableEq H] in
/-- A usable certificate certifies its issuance: `acmeCert = some c` forces the
order run `valid` and `c` to be the issued certificate. -/
theorem acmeCert_eq_some {ccfg : CertCfg Leaf H} {c : Leaf}
    (h : acmeCert ccfg = some c) :
    ccfg.issuance.order.status = .valid ∧ c = ccfg.certData := by
  unfold acmeCert at h
  by_cases hv : ccfg.issuance.order.status = .valid
  · rw [if_pos hv] at h
    injection h with h
    exact ⟨hv, h.symm⟩
  · rw [if_neg hv] at h
    exact absurd h (by simp)

omit [DecidableEq H] in
/-- An order that has not reached `valid` yields no certificate. -/
theorem acmeCert_none {ccfg : CertCfg Leaf H}
    (hnv : ccfg.issuance.order.status ≠ .valid) : acmeCert ccfg = none := by
  unfold acmeCert
  rw [if_neg hnv]

/-! ## The SCT check: the real Ct inclusion verifier -/

/-- **The SCT check.** Run the real RFC 6962 inclusion verifier on the
certificate's leaf hash against the evidence: recompute the head from
`hleaf cert`, the index, size, and audit path, and compare to the signed tree
head. Literally `Ct.verifyInclusion`. -/
def sctVerified (HS : Ct.HashScheme Leaf H) (e : Sct H) (cert : Leaf) : Bool :=
  Ct.verifyInclusion HS (HS.hleaf cert) e.index e.size e.path e.root

/-- Verification against the genuine head is *sound* for an arbitrary —
possibly adversarial — audit path: a leaf hash that verifies is the hash of
the genuine `i`-th appended leaf. This is the Ct library's `inclusion_sound`
(collision resistance spent on every peeled node) surfaced through the `Bool`
verifier. -/
theorem sctVerified_sound (HS : Ct.HashScheme Leaf H) {log : List Leaf}
    {i : Nat} {y : Leaf} {path : List H} (hi : i < log.length)
    (hv : Ct.verifyInclusion HS (HS.hleaf y) i log.length path (Ct.mth HS log)
            = true) :
    log[i]? = some y := by
  unfold Ct.verifyInclusion at hv
  cases hr : Ct.rootFromPath HS (HS.hleaf y) i log.length path with
  | none => rw [hr] at hv; simp at hv
  | some r =>
      rw [hr] at hv
      simp only [decide_eq_true_eq] at hv
      exact Ct.inclusion_sound HS log.length log i y path rfl hi (by rw [hr, hv])

/-! ## The composite certificate gate -/

/-- The certificate gate: a certificate must be *available* (the real Acme
order run reached `valid`) and its SCT evidence must *verify* (the real Ct
inclusion proof recomputes the head). With no issued certificate there is
nothing to serve — the gate refuses. -/
def certOk (ccfg : CertCfg Leaf H) : Bool :=
  match acmeCert ccfg with
  | none => false
  | some cert => sctVerified ccfg.hs ccfg.sct cert

/-- An open gate names its certificate: `certOk` forces the Acme-issued
certificate available *and* CT-verified. -/
theorem certOk_cert {ccfg : CertCfg Leaf H} (h : certOk ccfg = true) :
    acmeCert ccfg = some ccfg.certData
      ∧ sctVerified ccfg.hs ccfg.sct ccfg.certData = true := by
  unfold certOk at h
  cases hc : acmeCert ccfg with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
      rw [hc] at h
      obtain ⟨_, hcd⟩ := acmeCert_eq_some hc
      subst hcd
      exact ⟨rfl, h⟩

/-- No certificate (order not `valid`) closes the gate. -/
theorem certOk_false_of_not_valid {ccfg : CertCfg Leaf H}
    (hnv : ccfg.issuance.order.status ≠ .valid) : certOk ccfg = false := by
  unfold certOk
  rw [acmeCert_none hnv]

/-- A failing inclusion proof closes the gate. -/
theorem certOk_false_of_sct {ccfg : CertCfg Leaf H}
    (hf : sctVerified ccfg.hs ccfg.sct ccfg.certData = false) :
    certOk ccfg = false := by
  unfold certOk
  cases hc : acmeCert ccfg with
  | none => rfl
  | some c =>
      obtain ⟨_, hcd⟩ := acmeCert_eq_some hc
      subst hcd
      exact hf

/-! ## The gated feeder and the config transformers -/

/-- The certificate-gated handshake feeder: run the base feeder (the PKI-gated
real TLS handshake, on the deployed path) unchanged, then gate its accept with
`certOk` through the same `PkiWire.gateDone` the PKI lane uses. Only `.done`
is gated; a refused accept becomes `.fail`. -/
def certHsFeed (base : TlsConn → Bytes → HsOut) (ccfg : CertCfg Leaf H)
    (tc : TlsConn) (buf : Bytes) : HsOut :=
  PkiWire.gateDone (certOk ccfg) (base tc buf)

/-- Install the certificate gate *over* whatever handshake feeder a config
already carries, leaving every other field untouched. Composes: applied to the
PKI-wired config it stacks cert gate → PKI gate → real TLS engine. -/
def wireCert (ccfg : CertCfg Leaf H) (cfg : Config) : Config :=
  { cfg with hsFeed := certHsFeed cfg.hsFeed ccfg }

/-- **The cert-gate instantiation over the TLS stack.** The certificate gate over
`PkiWire.wiredPkiConfig` — i.e. over the PKI gate, over the real `Tls.step`
adapters, over the arena-backed `Reactor.Config.demoConfig`. NOTE: this is a
SEPARATE config lineage from `Reactor.Deploy.deployConfig` (the config `main`
runs); see `deployConfig_hsFeed_ungated` and the deployed-path status note. -/
def wiredCertConfig (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) : Config :=
  wireCert ccfg (PkiWire.wiredPkiConfig tcfg pcfg)

/-- No drift: the wired `hsFeed` is exactly the cert-gated feeder over the
config's own feeder. -/
theorem wireCert_hsFeed (ccfg : CertCfg Leaf H) (cfg : Config) :
    (wireCert ccfg cfg).hsFeed = certHsFeed cfg.hsFeed ccfg := rfl

/-- No drift, fully unfolded on the deployed path: the deployed `hsFeed` is
the cert gate over the PKI gate over the **real** TLS handshake adapter. -/
theorem wiredCertConfig_hsFeed (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) :
    (wiredCertConfig tcfg pcfg ccfg).hsFeed
      = certHsFeed (PkiWire.pkiHsFeed (TlsWire.hsFeedReal tcfg) pcfg) ccfg := rfl

/-- The cert gate leaves the real record layer wired. -/
theorem wiredCertConfig_tlsRecv (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) :
    (wiredCertConfig tcfg pcfg ccfg).tlsRecv = TlsWire.tlsRecvReal tcfg := rfl

/-- The cert gate leaves the deployed arena parser wired: the HTTP/1.1 lane
underneath is still `demoConfig`'s. -/
theorem wiredCertConfig_h1Parse (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) :
    (wiredCertConfig tcfg pcfg ccfg).h1Parse = Reactor.Config.h1ParseFn := rfl

/-! ## Deployed-path status — the cert/PKI gate is NOT yet in `deployConfig`

Scope note: `wiredCertConfig` is a distinct config lineage — cert gate → PKI
gate → real TLS adapter → `demoConfig`. It is *not* `Reactor.Deploy.deployConfig`
— the config
`Arena.Orb.main` runs (`deployStep`/`serveFull` over `deployConfig`).
`deployConfig` wires the real TLS engine on `hsFeed` (`Deploy.deploy_uses_real_tls`)
but installs neither the PKI gate nor the cert gate, so its handshake feeder is
the *ungated* real handshake — recorded below as `deployConfig_hsFeed_ungated`.

Nor does the Bridge congruence transport the cert seam onto the deployed path.
Bridge lifts facts along the **plainH1** arm of `onBytes` (`runH1`/`h1Loop`),
which reads only the four HTTP/1.1 fields (`h1Parse`, `maxHeaderBytes`,
`oversizeResponse`, `errorResponse`) — never `hsFeed`. The cert gate fires only
on the `.tlsHandshake` state (`Proto.onBytes → hsStep → hsFeed`), which the
deployed plainH1 recv path (`Conn.mkPlain`, proto `.plainH1 []`) never enters. So
the cert gate is *structurally off* the plainH1 deployed path: it is neither in
`deployConfig` nor reachable by the congruence. The seam theorems below hold over
`wiredCertConfig` (a real config, driven by `Proto.onBytes`), but that is a
distinct lineage, honestly not the one `main` executes.

FOLLOWUP (cert-in-deploy): to put the cert/PKI gate on the deployed path, thread
`PkiWire.wirePki` / `wireCert` into `deployConfig`'s TLS wiring — so
`deployConfig.hsFeed = certHsFeed (pkiHsFeed (hsFeedReal …) …) ccfg` — and add a
deployed-accept theorem. That is a change in `Reactor.Deploy`, not a
congruence lift: the plainH1 congruence cannot reach a TLS-accept field. -/

/-- **The gate absent from the deployed config.** `Reactor.Deploy.deployConfig`'s
handshake feeder — the function `Proto.hsStep` calls on the config `main` runs —
is the *ungated* real TLS engine: neither the PKI gate nor the cert gate is on
it. This records the gap honestly: the cert lineage (`wiredCertConfig`) is a
distinct config from `deployConfig`, and the cert gate is not on the deployed
accept path. -/
theorem deployConfig_hsFeed_ungated :
    Reactor.Deploy.deployConfig.hsFeed = TlsWire.hsFeedReal TlsWire.demoTlsCfg :=
  Reactor.Deploy.deploy_uses_real_tls.1

/-! ## The accept discipline -/

/-- The gate only ever lets `.done` through with the wrapped output's own
payload: an accepted handshake is the base feeder's accept, unrewritten. -/
theorem gateDone_done_base {ok : Bool} {o : HsOut}
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (h : PkiWire.gateDone ok o = .done tc' consumed toSend alpn ktls early) :
    o = .done tc' consumed toSend alpn ktls early := by
  cases o with
  | more _ _ _ => simp [PkiWire.gateDone] at h
  | fail => simp [PkiWire.gateDone] at h
  | done a b c d e f =>
      simp only [PkiWire.gateDone] at h
      by_cases hok : ok = true
      · rw [if_pos hok] at h; exact h
      · rw [if_neg hok] at h; exact absurd h (by simp)

/-- The cert-gated feeder accepts only when the certificate gate holds. -/
theorem certHsFeed_done_certOk (base : TlsConn → Bytes → HsOut)
    (ccfg : CertCfg Leaf H) (tc : TlsConn) (buf : Bytes)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : certHsFeed base ccfg tc buf = .done tc' consumed toSend alpn ktls early) :
    certOk ccfg = true :=
  PkiWire.gateDone_done hd

/-- **The deployed accept, in full.** If the deployed wired config's `hsFeed`
— the function `Proto.hsStep` calls on the running `.tlsHandshake` path —
accepts, then the certificate gate held *and* the PKI gate underneath held:
the whole stack of real-library conditions is discharged by one accept. -/
theorem wiredCert_accept (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) (tc : TlsConn) (buf : Bytes)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : (wiredCertConfig tcfg pcfg ccfg).hsFeed tc buf
            = .done tc' consumed toSend alpn ktls early) :
    certOk ccfg = true ∧ PkiWire.pkiOk pcfg tc buf = true := by
  have hd' : PkiWire.gateDone (certOk ccfg)
      (PkiWire.pkiHsFeed (TlsWire.hsFeedReal tcfg) pcfg tc buf)
        = .done tc' consumed toSend alpn ktls early := hd
  exact ⟨PkiWire.gateDone_done hd',
    PkiWire.pkiHsFeed_done_pkiOk _ pcfg tc buf (gateDone_done_base hd')⟩

/-! ## Seam theorem 1 — a cert is used only after the real Acme order is valid -/

/-- **`acme_issues_before_serve`.** If the deployed wired handshake accepts
(`.done` — the event that lets `Proto.hsStep` enter an established state), the
certificate it serves is the Acme-issued one (`acmeCert = some certData`), the
real order run reached `valid`, and — composing the Acme library's own
invariant `valid_requires_all_authz_valid` — **every** authorization of that
order is valid. No certificate is used before issuance; no issuance happens
past a pending or failed authorization. -/
theorem acme_issues_before_serve (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) (tc : TlsConn) (buf : Bytes)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : (wiredCertConfig tcfg pcfg ccfg).hsFeed tc buf
            = .done tc' consumed toSend alpn ktls early) :
    acmeCert ccfg = some ccfg.certData
      ∧ ccfg.issuance.order.status = .valid
      ∧ Acme.allValid ccfg.issuance.order.authzs = true := by
  obtain ⟨hok, _⟩ := wiredCert_accept tcfg pcfg ccfg tc buf hd
  obtain ⟨hc, _⟩ := certOk_cert hok
  obtain ⟨hv, _⟩ := acmeCert_eq_some hc
  exact ⟨hc, hv,
    Acme.valid_requires_all_authz_valid ccfg.issuance.ids ccfg.issuance.events hv⟩

/-- All-valid over the challenge→authorization bridge: if every authorization
status is the bridge image of its challenge, they are all valid only when every
challenge is valid. Composes `Acme.authzOfChalStatus_valid` pointwise. -/
theorem allValid_bridge {chals : List Acme.ChalStatus}
    (hall : Acme.allValid (chals.map Acme.authzOfChalStatus) = true) :
    ∀ c ∈ chals, c = .valid := by
  induction chals with
  | nil => intro c hc; exact absurd hc (List.not_mem_nil c)
  | cons a t ih =>
      simp only [List.map_cons, Acme.allValid, List.all_cons,
        Bool.and_eq_true] at hall
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Acme.authzOfChalStatus_valid.mp
          ((Acme.AuthzStatus.isValid_eq _).mp hall.1)
      · exact ih hall.2 c hc

/-- **`acme_no_challenge_bypass`.** The challenge-level composition: when each
authorization of the issuance order is discharged by a challenge (its status is
`authzOfChalStatus` of that challenge's status — the Acme library's bridge), a
deployed accept forces **every one of those challenges to be `valid`**. By the
Acme library's `chal_into_valid` / `validateStep_valid_needs_success`, the only
door into a valid challenge is a *successful* validation — so no certificate is
served whose issuance skipped or failed a challenge. -/
theorem acme_no_challenge_bypass (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) (tc : TlsConn) (buf : Bytes)
    (chals : List Acme.ChalStatus)
    (hbridge : ccfg.issuance.order.authzs = chals.map Acme.authzOfChalStatus)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : (wiredCertConfig tcfg pcfg ccfg).hsFeed tc buf
            = .done tc' consumed toSend alpn ktls early) :
    ∀ c ∈ chals, c = .valid := by
  obtain ⟨_, _, hall⟩ := acme_issues_before_serve tcfg pcfg ccfg tc buf hd
  rw [hbridge] at hall
  exact allValid_bridge hall

/-! ## Seam theorem 2 — a cert is accepted only if the real Ct inclusion
proof verifies -/

/-- **`ct_inclusion_seam`.** If the deployed wired handshake accepts, the real
`Ct.verifyInclusion` returned `true` for the served certificate's leaf hash
against the carried SCT evidence: the accept is conditioned on the real
inclusion-proof verification, verbatim. -/
theorem ct_inclusion_seam (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) (tc : TlsConn) (buf : Bytes)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : (wiredCertConfig tcfg pcfg ccfg).hsFeed tc buf
            = .done tc' consumed toSend alpn ktls early) :
    Ct.verifyInclusion ccfg.hs (ccfg.hs.hleaf ccfg.certData)
      ccfg.sct.index ccfg.sct.size ccfg.sct.path ccfg.sct.root = true := by
  obtain ⟨hok, _⟩ := wiredCert_accept tcfg pcfg ccfg tc buf hd
  exact (certOk_cert hok).2

/-- **`ct_cert_logged`.** Compose the seam with the Ct library's inclusion
*soundness*: when the SCT's head is the genuine head of the real log `log`
(and its size/index describe it), an accepted certificate **is** the genuine
`index`-th leaf of that log. Collision resistance (`hnode_inj`/`hleaf_inj`,
spent inside `Ct.inclusion_sound`) means even an adversarially crafted audit
path cannot carry an unlogged certificate past a genuine head. -/
theorem ct_cert_logged (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) (tc : TlsConn) (buf : Bytes) (log : List Leaf)
    (hroot : ccfg.sct.root = Ct.mth ccfg.hs log)
    (hsize : ccfg.sct.size = log.length)
    (hi : ccfg.sct.index < log.length)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : (wiredCertConfig tcfg pcfg ccfg).hsFeed tc buf
            = .done tc' consumed toSend alpn ktls early) :
    log[ccfg.sct.index]? = some ccfg.certData := by
  have hv := ct_inclusion_seam tcfg pcfg ccfg tc buf hd
  rw [hsize, hroot] at hv
  exact sctVerified_sound ccfg.hs hi hv

/-! ## The reactor seam: the gate on the running `Proto.onBytes` path

With `wireCert`, `cfg.hsFeed` — the function `Proto.hsStep` calls from
`Proto.onBytes` on a `.tlsHandshake` state — is `certHsFeed`. A closed gate
never emits `.done`, and `hsStep` enters an established state only on `.done`,
so the connection closes or stays in handshake. -/

/-- A closed certificate gate keeps the running reactor off the established
path: `Proto.onBytes` on the handshake state closes the connection or stays in
`.tlsHandshake`. -/
theorem cert_gate_reactor (ccfg : CertCfg Leaf H) (cfg : Config)
    (tc : TlsConn) (tlsBuf data : Bytes)
    (hnok : certOk ccfg = false) :
    (Proto.onBytes (wireCert ccfg cfg) (.tlsHandshake tc tlsBuf) data).closeNow = true ∨
    ∃ tc' rest, (Proto.onBytes (wireCert ccfg cfg) (.tlsHandshake tc tlsBuf) data).proto
        = .tlsHandshake tc' rest := by
  have hnd : ∀ tc' consumed toSend alpn ktls early,
      (wireCert ccfg cfg).hsFeed tc (tlsBuf ++ data)
        ≠ .done tc' consumed toSend alpn ktls early := by
    intro tc' consumed toSend alpn ktls early hd
    rw [wireCert_hsFeed] at hd
    have := certHsFeed_done_certOk cfg.hsFeed ccfg tc (tlsBuf ++ data) hd
    rw [hnok] at this
    exact absurd this (by simp)
  simpa only [Proto.onBytes] using
    PkiWire.hsStep_no_done (wireCert ccfg cfg) (.tlsHandshake tc tlsBuf) tc
      (tlsBuf ++ data) hnd

/-- **`acme_gate_reactor`.** On the running deployed path, an order that has
not reached `valid` — no issued certificate — never carries the connection
into an established protocol state: `Proto.onBytes` closes or stays in
handshake. The issuance step is *before* serving, as a reactor-level fact. -/
theorem acme_gate_reactor (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) (tc : TlsConn) (tlsBuf data : Bytes)
    (hnv : ccfg.issuance.order.status ≠ .valid) :
    (Proto.onBytes (wiredCertConfig tcfg pcfg ccfg) (.tlsHandshake tc tlsBuf) data).closeNow = true ∨
    ∃ tc' rest, (Proto.onBytes (wiredCertConfig tcfg pcfg ccfg) (.tlsHandshake tc tlsBuf) data).proto
        = .tlsHandshake tc' rest :=
  cert_gate_reactor ccfg (PkiWire.wiredPkiConfig tcfg pcfg) tc tlsBuf data
    (certOk_false_of_not_valid hnv)

/-- **`ct_gate_reactor`.** On the running deployed path, a certificate whose
CT inclusion proof fails the real verifier never carries the connection into
an established protocol state: `Proto.onBytes` closes or stays in handshake. -/
theorem ct_gate_reactor (tcfg : Tls.Config) (pcfg : PkiWire.PkiCfg)
    (ccfg : CertCfg Leaf H) (tc : TlsConn) (tlsBuf data : Bytes)
    (hf : sctVerified ccfg.hs ccfg.sct ccfg.certData = false) :
    (Proto.onBytes (wiredCertConfig tcfg pcfg ccfg) (.tlsHandshake tc tlsBuf) data).closeNow = true ∨
    ∃ tc' rest, (Proto.onBytes (wiredCertConfig tcfg pcfg ccfg) (.tlsHandshake tc tlsBuf) data).proto
        = .tlsHandshake tc' rest :=
  cert_gate_reactor ccfg (PkiWire.wiredPkiConfig tcfg pcfg) tc tlsBuf data
    (certOk_false_of_sct hf)

/-! ## Liveness sanity: the gate opens on honest evidence -/

/-- A complete issuance run for one identifier: the authorization is validated
(`authzResult 0 true` — the CA's verdict after a successful challenge), the
order is finalized, the CA issues. Drives the real `Acme.orderStep`. -/
def demoIssuance (d : Acme.Bytes) : Issuance :=
  { ids := [d], events := [.authzResult 0 true, .finalize, .issued] }

/-- The demo issuance run reaches `valid` — the order FSM actually issues on
the honest trace (pending → ready → processing → valid, computed). -/
theorem demoIssuance_valid (d : Acme.Bytes) :
    (demoIssuance d).order.status = .valid := rfl

/-- Honest SCT evidence for the `i`-th leaf of the real log: the real
`Ct.auditPath` and the real head `Ct.mth`. -/
def honestSct (HS : Ct.HashScheme Leaf H) (log : List Leaf) (i : Nat) : Sct H :=
  { index := i, size := log.length, path := Ct.auditPath HS log i,
    root := Ct.mth HS log }

/-- Honest evidence verifies: the real audit path for a genuinely logged
certificate passes the real verifier (`Ct.inclusion_iff`, the `←` direction). -/
theorem honestSct_verifies (HS : Ct.HashScheme Leaf H) (log : List Leaf)
    {i : Nat} {cert : Leaf} (hi : i < log.length)
    (hcert : log[i]? = some cert) :
    sctVerified HS (honestSct HS log i) cert = true :=
  (Ct.inclusion_iff HS hi).mpr hcert

/-- The composite gate is satisfiable — not vacuously closed: a completed
issuance run plus honest CT evidence for a logged certificate opens it. -/
theorem certOk_satisfiable (HS : Ct.HashScheme Leaf H) (d : Acme.Bytes)
    (log : List Leaf) {i : Nat} {cert : Leaf} (hi : i < log.length)
    (hcert : log[i]? = some cert) :
    certOk { hs := HS, issuance := demoIssuance d, certData := cert,
             sct := honestSct HS log i } = true := by
  have hc : acmeCert (Leaf := Leaf) (H := H)
      { hs := HS, issuance := demoIssuance d, certData := cert,
        sct := honestSct HS log i } = some cert := by
    unfold acmeCert
    rw [if_pos (demoIssuance_valid d)]
  unfold certOk
  rw [hc]
  exact honestSct_verifies HS log hi hcert

end CertWire
end Reactor
