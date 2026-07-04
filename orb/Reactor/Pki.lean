import Reactor.Tls
import Resume.Ticket
import Resume.Ocsp
import Mtls.Verify
import Mtls.Theorems

/-!
# Reactor.Pki — wiring the real PKI libraries into the TLS accept decision

`Reactor.Tls` drove the real `Tls` record/handshake machine through the FSM's
opaque `TlsConn` handle: `hsFeedReal` turns the handshake engine's phase into
the FSM's `HsOut` (`.more` while handshaking, `.done` on completion, `.fail` on
teardown), and `wireTls` installs it into `Config.hsFeed`. That is the function
the running reactor calls on every `.tlsHandshake` byte (`Proto.onBytes →
Proto.hsStep → cfg.hsFeed`).

This file gates that **accept decision** with two real PKI libraries, at the one
place the handshake completes:

* **Resume** (`Resume.Ticket`, `Resume.Ocsp`) — when a returning client presents
  a session-resumption ticket, the real validity-window logic (`Resume.accept`)
  decides whether resumption is honoured; a ticket outside `[issued, expiry)` (or
  under a rotated key epoch) is refused. If the server carries a stapled OCSP
  response, the real freshness gate (`Resume.Staple.fresh`) refuses to complete
  the handshake with a stale staple.

* **Mtls** (`Mtls.Verify`, `Mtls.Theorems`) — when a client presents a
  certificate chain (mutual TLS), the real path validator (`Mtls.authenticate`,
  built on `Mtls.verifyFrom`) derives the single client identity, or yields none.
  When mTLS is required, the handshake completes only if that validation
  succeeds — there is no path from a failed chain to an authenticated session.

Neither library is a dependency of the other or of `Tls`; each surfaces its
input (ticket, staple, chain) to this gate, which composes them *over* the real
TLS accept.

## The wiring

`pkiHsFeed base pcfg` wraps a base handshake feeder (the real
`TlsWire.hsFeedReal tcfg`): it runs the underlying TLS handshake unchanged and,
**only** on `.done` (the accept), applies the PKI gate `pkiOk`. If any gate
refuses, the accept is turned into `.fail` — the handshake does not complete.
`.more` (still handshaking) and `.fail` (already refused) pass through untouched.

`wirePki tcfg pcfg cfg` installs `pkiHsFeed (hsFeedReal tcfg) pcfg` into
`Config.hsFeed`, so the *running* reactor invokes it: `Proto.onBytes` on a
`.tlsHandshake` state calls `Proto.hsStep`, which calls `cfg.hsFeed` — now the
PKI-gated feeder. `wiredPkiConfig` is the concrete reactor config with the real
TLS engine and the PKI gate both plugged in over the arena-backed HTTP/1.1
`demoConfig`.

## The seam theorems

* `pki_resume_window` — if a session ticket is presented and the wired handshake
  accepts (`.done`), the current time lies inside the ticket's validity window
  per the real `Resume.accept_in_window`. Its reactor form
  (`pki_resume_window_reactor`) shows that on the running `Proto.onBytes` path a
  ticket outside its window can never carry the connection into an established
  protocol state — the reactor closes or stays in handshake.
* `mtls_no_auth_on_failure` — with mTLS required, a chain that fails the real
  `Mtls.verifyFrom` validation never lets the wired handshake reach `.done`
  (composing `Mtls.authenticate_unverified` with the gate);
  `mtls_identity_verified` shows any derived identity comes only from a validated
  chain (`Mtls.authenticate_eq_some`). The reactor form
  (`mtls_no_auth_on_failure_reactor`) transports this to `Proto.onBytes`: a
  failed chain yields no authenticated established state.
* `pki_ocsp_fresh` — if the wired handshake accepts while a staple is configured,
  that staple was fresh (`now < nextUpdate`) per the real `Resume.fresh_iff`.
-/

namespace Reactor
namespace PkiWire

open Proto (Bytes TlsConn Config HsOut)

/-! ## The PKI accept context: the credentials surfaced to the gate -/

/-- The static PKI context threaded into the handshake accept decision. The
`ticketOf`/`chainOf` fields surface the client-presented credentials (session
ticket, certificate chain) out of the handshake handle and buffer — the sibling
libraries' *inputs* — the same shape by which `Tls.Config` surfaces the crypto
boundary. Every function-valued field is total, so the seam theorems hold
uniformly over every presentation behaviour. -/
structure PkiCfg where
  /-- The check time for every window/freshness decision. -/
  now : Nat
  /-- The current session-ticket key epoch (a rotated key advances it). -/
  resumeEpoch : Nat
  /-- The server's current stapled OCSP response, if it staples. -/
  staple : Option Resume.Staple
  /-- The mTLS verification context: the named signature interface and the
  trust-anchor set. -/
  mtlsEnv : Mtls.Env
  /-- Whether client-certificate authentication is required to complete. -/
  mtlsRequired : Bool
  /-- The session-resumption ticket the client presented, if any. -/
  ticketOf : TlsConn → Bytes → Option Resume.Ticket
  /-- The client certificate chain the client presented (leaf first). -/
  chainOf : TlsConn → Bytes → Mtls.Chain

/-! ## The individual gates, each a call into a real library -/

/-- The client identity the real `Mtls` validator derives from the presented
chain: `some subject` on a validated chain, `none` otherwise. This is literally
`Mtls.authenticate`. -/
def mtlsIdentity (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : Option Mtls.Name :=
  Mtls.authenticate pcfg.mtlsEnv pcfg.now (pcfg.chainOf tc buf)

/-- The resumption gate: with no ticket presented this is a full (non-resumed)
handshake and passes; with a ticket, the real `Resume.accept` decides it against
the validity window and key epoch. -/
def resumeOk (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : Bool :=
  match pcfg.ticketOf tc buf with
  | none => true
  | some t => Resume.accept t pcfg.now pcfg.resumeEpoch

/-- The OCSP gate: with no staple configured this passes; with a staple, the
real `Resume.Staple.fresh` refuses a stale one. -/
def ocspOk (pcfg : PkiCfg) : Bool :=
  match pcfg.staple with
  | none => true
  | some s => s.fresh pcfg.now

/-- The mTLS gate: when client-cert auth is required, an identity must have been
derived (i.e. the chain validated); otherwise it passes. -/
def mtlsOk (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : Bool :=
  if pcfg.mtlsRequired then (mtlsIdentity pcfg tc buf).isSome else true

/-- The composite accept gate: every PKI condition must hold to honour the
handshake. -/
def pkiOk (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : Bool :=
  resumeOk pcfg tc buf && ocspOk pcfg && mtlsOk pcfg tc buf

/-! ## The gated feeder and the config transformer -/

/-- Apply the accept gate to one `HsOut`: only `.done` (the accept) is gated;
`.more`/`.fail` pass through. A refused accept becomes `.fail`. -/
def gateDone (ok : Bool) : HsOut → HsOut
  | .done tc consumed toSend alpn ktls early =>
      if ok then .done tc consumed toSend alpn ktls early else .fail
  | out => out

/-- The PKI-gated handshake feeder: run the base (real TLS) handshake, then gate
its accept with `pkiOk`. This is the function installed on the reactor path. -/
def pkiHsFeed (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes) : HsOut :=
  gateDone (pkiOk pcfg tc buf) (base tc buf)

/-- Install the PKI-gated feeder over the **real** TLS handshake adapter into a
base `Proto.Config`, leaving every other field (including the real `tlsRecv`/
`tlsSend`) untouched. -/
def wirePki (tcfg : Tls.Config) (pcfg : PkiCfg) (cfg : Config) : Config :=
  { cfg with hsFeed := pkiHsFeed (TlsWire.hsFeedReal tcfg) pcfg }

/-- The concrete reactor config with the real TLS engine and the PKI accept gate
both wired in over the arena-backed HTTP/1.1 `demoConfig`. -/
def wiredPkiConfig (tcfg : Tls.Config) (pcfg : PkiCfg) : Config :=
  wirePki tcfg pcfg (TlsWire.wireTls tcfg Reactor.Config.demoConfig)

/-- No drift: the wired `hsFeed` is exactly the PKI-gated feeder over the real
TLS handshake adapter. -/
theorem wirePki_hsFeed (tcfg : Tls.Config) (pcfg : PkiCfg) (cfg : Config) :
    (wirePki tcfg pcfg cfg).hsFeed = pkiHsFeed (TlsWire.hsFeedReal tcfg) pcfg := rfl

/-- The PKI gate leaves the real record layer wired: `tlsRecv`/`tlsSend` come
straight from the TLS engine. -/
theorem wiredPkiConfig_tlsRecv (tcfg : Tls.Config) (pcfg : PkiCfg) :
    (wiredPkiConfig tcfg pcfg).tlsRecv = TlsWire.tlsRecvReal tcfg := rfl

/-! ## The accept-gate discipline: `.done` implies `pkiOk` -/

/-- The gate only ever emits `.done` when `ok` holds. -/
theorem gateDone_done {ok : Bool} {o : HsOut}
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (h : gateDone ok o = .done tc' consumed toSend alpn ktls early) : ok = true := by
  cases o with
  | more _ _ _ => simp [gateDone] at h
  | fail => simp [gateDone] at h
  | done _ _ _ _ _ _ =>
    simp only [gateDone] at h
    by_cases hok : ok = true
    · exact hok
    · rw [if_neg hok] at h; exact absurd h (by simp)

/-- **The accept discipline.** The wired feeder accepts (`.done`) only when the
composite PKI gate holds. -/
theorem pkiHsFeed_done_pkiOk (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : pkiHsFeed base pcfg tc buf = .done tc' consumed toSend alpn ktls early) :
    pkiOk pcfg tc buf = true :=
  gateDone_done hd

/-! ### Projecting the composite gate onto its three conjuncts -/

theorem pkiOk_resume {pcfg : PkiCfg} {tc : TlsConn} {buf : Bytes}
    (h : pkiOk pcfg tc buf = true) : resumeOk pcfg tc buf = true := by
  unfold pkiOk at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

theorem pkiOk_ocsp {pcfg : PkiCfg} {tc : TlsConn} {buf : Bytes}
    (h : pkiOk pcfg tc buf = true) : ocspOk pcfg = true := by
  unfold pkiOk at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

theorem pkiOk_mtls {pcfg : PkiCfg} {tc : TlsConn} {buf : Bytes}
    (h : pkiOk pcfg tc buf = true) : mtlsOk pcfg tc buf = true := by
  unfold pkiOk at h
  exact (Bool.and_eq_true_iff.mp h).2

/-! ## Seam theorem 1 — resumption only inside the validity window -/

/-- **`pki_resume_window`.** If a session-resumption ticket is presented and the
wired handshake *accepts* it (surfaces `.done`), then the current time lies
inside the ticket's half-open validity window `[issued, expiry)`. This composes
the real `Resume.accept_in_window` with the TLS accept: the accept could only
have fired because `resumeOk` held, and with a ticket present `resumeOk` *is*
`Resume.accept`, whose window theorem transfers verbatim. -/
theorem pki_resume_window (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes) (t : Resume.Ticket)
    (ht : pcfg.ticketOf tc buf = some t)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : pkiHsFeed base pcfg tc buf = .done tc' consumed toSend alpn ktls early) :
    t.issued ≤ pcfg.now ∧ pcfg.now < t.expiry := by
  have hres := pkiOk_resume (pkiHsFeed_done_pkiOk base pcfg tc buf hd)
  simp only [resumeOk, ht] at hres
  exact Resume.accept_in_window hres

/-! ## Seam theorem 2 — no client identity / no accept on chain failure -/

/-- Any client identity the gate derives comes only from a chain the real
validator accepted — the no-bypass property (`Mtls.authenticate_eq_some`)
transported to the reactor's `mtlsIdentity`. -/
theorem mtls_identity_verified (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes)
    {id : Mtls.Name} (h : mtlsIdentity pcfg tc buf = some id) :
    Mtls.verifyFrom pcfg.mtlsEnv pcfg.now (pcfg.chainOf tc buf) = true := by
  obtain ⟨_, _, _, _, hver⟩ := Mtls.authenticate_eq_some h
  exact hver

/-- **`mtls_no_auth_on_failure`.** With mTLS required, a client chain that fails
the real `Mtls.verifyFrom` validation never lets the wired handshake reach
`.done`: no authenticated session is established on a failed chain. This composes
`Mtls.authenticate_unverified` (a failed chain yields no identity) with the
accept gate (a required-but-absent identity refuses the accept). -/
theorem mtls_no_auth_on_failure (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes)
    (hreq : pcfg.mtlsRequired = true)
    (hfail : Mtls.verifyFrom pcfg.mtlsEnv pcfg.now (pcfg.chainOf tc buf) = false)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes} :
    pkiHsFeed base pcfg tc buf ≠ .done tc' consumed toSend alpn ktls early := by
  intro hd
  have hm := pkiOk_mtls (pkiHsFeed_done_pkiOk base pcfg tc buf hd)
  have hnone : mtlsIdentity pcfg tc buf = none := Mtls.authenticate_unverified hfail
  unfold mtlsOk at hm
  rw [if_pos hreq, hnone] at hm
  simp at hm

/-! ## Seam theorem 3 — no accept on a stale OCSP staple -/

/-- **`pki_ocsp_fresh`.** If the wired handshake accepts while the server carries
a stapled OCSP response, that staple was fresh at the check time
(`thisUpdate ≤ now < nextUpdate`) per the real `Resume.fresh_iff` — a stale
staple can never ride out on an accepted handshake. -/
theorem pki_ocsp_fresh (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes) (s : Resume.Staple)
    (hs : pcfg.staple = some s)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : pkiHsFeed base pcfg tc buf = .done tc' consumed toSend alpn ktls early) :
    s.thisUpdate ≤ pcfg.now ∧ pcfg.now < s.nextUpdate := by
  have hoc := pkiOk_ocsp (pkiHsFeed_done_pkiOk base pcfg tc buf hd)
  simp only [ocspOk, hs] at hoc
  exact (Resume.fresh_iff s pcfg.now).mp hoc

/-! ## The reactor seam: the gate is invoked on the running `onBytes` path

`Proto.onBytes` on a `.tlsHandshake` state calls `Proto.hsStep`, which calls
`cfg.hsFeed`. With `wirePki`, that field is `pkiHsFeed`. A gate that never emits
`.done` therefore cannot carry `hsStep` into an established protocol state:
`hsStep` enters `runH1`/`runH2` (an established state) only on `.done`, so on
`.more` it stays in `.tlsHandshake` and on `.fail` it closes. -/

/-- A handshake feeder that never accepts keeps the running `hsStep` off the
established path: it either closes the connection or stays in the handshake. -/
theorem hsStep_no_done (cfg : Config) (stay : Proto.ProtoState)
    (tc : TlsConn) (buf : Bytes)
    (hnd : ∀ tc' consumed toSend alpn ktls early,
      cfg.hsFeed tc buf ≠ .done tc' consumed toSend alpn ktls early) :
    (Proto.hsStep cfg none stay tc buf).closeNow = true ∨
    ∃ tc' rest, (Proto.hsStep cfg none stay tc buf).proto = .tlsHandshake tc' rest := by
  unfold Proto.hsStep
  cases hh : cfg.hsFeed tc buf with
  | more a b c => exact Or.inr ⟨a, buf.drop b, rfl⟩
  | fail => exact Or.inl rfl
  | done a b c d e f => exact absurd hh (hnd a b c d e f)

/-- **`mtls_no_auth_on_failure_reactor`.** On the running reactor path, an mTLS
handshake whose presented chain fails the real validation never reaches an
established protocol state: `Proto.onBytes` on the `.tlsHandshake` state either
closes the connection or leaves it still handshaking. Composes
`mtls_no_auth_on_failure` with `Proto.onBytes`/`Proto.hsStep`. -/
theorem mtls_no_auth_on_failure_reactor (tcfg : Tls.Config) (pcfg : PkiCfg)
    (cfg : Config) (tc : TlsConn) (tlsBuf data : Bytes)
    (hreq : pcfg.mtlsRequired = true)
    (hfail : Mtls.verifyFrom pcfg.mtlsEnv pcfg.now
              (pcfg.chainOf tc (tlsBuf ++ data)) = false) :
    (Proto.onBytes (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) data).closeNow = true ∨
    ∃ tc' rest, (Proto.onBytes (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) data).proto
        = .tlsHandshake tc' rest := by
  have hnd : ∀ tc' consumed toSend alpn ktls early,
      (wirePki tcfg pcfg cfg).hsFeed tc (tlsBuf ++ data)
        ≠ .done tc' consumed toSend alpn ktls early := by
    intro tc' consumed toSend alpn ktls early
    rw [wirePki_hsFeed]
    exact mtls_no_auth_on_failure _ pcfg tc (tlsBuf ++ data) hreq hfail
  simpa only [Proto.onBytes] using
    hsStep_no_done (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) tc (tlsBuf ++ data) hnd

/-- **`pki_resume_window_reactor`.** On the running reactor path, a resumption
ticket presented outside its validity window never carries the connection into
an established protocol state: `Proto.onBytes` closes or stays in handshake.
Composes `pki_resume_window` with `Proto.onBytes`/`Proto.hsStep`. -/
theorem pki_resume_window_reactor (tcfg : Tls.Config) (pcfg : PkiCfg)
    (cfg : Config) (tc : TlsConn) (tlsBuf data : Bytes) (t : Resume.Ticket)
    (ht : pcfg.ticketOf tc (tlsBuf ++ data) = some t)
    (hbad : ¬ (t.issued ≤ pcfg.now ∧ pcfg.now < t.expiry)) :
    (Proto.onBytes (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) data).closeNow = true ∨
    ∃ tc' rest, (Proto.onBytes (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) data).proto
        = .tlsHandshake tc' rest := by
  have hnd : ∀ tc' consumed toSend alpn ktls early,
      (wirePki tcfg pcfg cfg).hsFeed tc (tlsBuf ++ data)
        ≠ .done tc' consumed toSend alpn ktls early := by
    intro tc' consumed toSend alpn ktls early
    rw [wirePki_hsFeed]
    intro hd
    exact hbad (pki_resume_window _ pcfg tc (tlsBuf ++ data) t ht hd)
  simpa only [Proto.onBytes] using
    hsStep_no_done (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) tc (tlsBuf ++ data) hnd

end PkiWire
end Reactor
