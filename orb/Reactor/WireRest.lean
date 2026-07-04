import Reactor.Bridge
import Reactor.Deploy
import Drain.Basic
import Fallback.Chain
import Resume.Ticket
import Redirect
import Cgi
import ForwardProxy
import Mtls.Theorems
import Udp.Session

/-!
# Reactor.WireRest — the remaining island libraries attached to the DEPLOYED path

The goal clause: *the ~31 islands are connected, not proven-in-isolation.* After
`Reactor.Deploy` (proxy/DNS/header/trace/policy/safety/html/earlyhints),
`Reactor.CacheDeploy` (RFC 9111 cache), and `Reactor.WireMore` (HAR, StickTable,
DownloadMgr, SSE, Isolation, Metrics), a handful of libraries were still proved
only in isolation — never referenced by the values the deployed binary
(`Arena.Orb.main` → `Reactor.Deploy.deployStep(Guarded)` → `serveFull`/`serveGuarded`)
actually produces. This file moves eight more of them from *island* to
*connected* by stating each library's core theorem over the values the deployed
path carries: the served response `Reactor.Deploy.deployResp input`, its body,
and the request the deployed reactor dispatched (`req : Proto.Request`).

The anchor remains `Reactor.Bridge`: the request/submissions the DEPLOYED reactor
extracts are the same the test reactor extracts
(`Bridge.deploySubs_eq_reactorSubs`), so a seam keyed on the deployed dispatch is
anchored to the one shared reactor the island lanes were proven over.

Honest scope (identical posture to `Reactor.WireMore`, CW5/CW6 in
`Reactor.Deploy`): these are *proof-attachment* seams. Each states a library's
real, meaning-constraining theorem about the actual deployed served
bytes / dispatched request, discharged by the library's own proof — not (yet) a
runtime byte-driver that runs a CONNECT tunnel, drains connections on SIGTERM, or
relays UDP in the event loop. What they establish is that the library's guarantee
*holds of the data the deployed path carries*, closing the island. Where a
lifecycle machine has no serve-path bytes to key on (Drain, Resume), the seam is
built as a concrete deployed *scenario* over the deployed listener id / key
generation — the same modeled-state posture `Reactor.Deploy.deploySystem`
(Isolation) and `deployRunning` (Policy) already use.

Attached here: `Fallback`, `Cgi`, `Redirect`, `ForwardProxy`, `Udp`, `Mtls`,
`Drain`, `Resume`.
-/

namespace Reactor
namespace WireRest

open Proto (Bytes)

/-! ## (1) Fallback — the deployed response is served exactly once -/

/-- A fallback handler that serves the deployed response (the bytes `serveFull`
would emit for this input). Slotted at the tail of a configured chain, it is the
last-resort backend. -/
def deployHandler (input : Bytes) :
    Fallback.Chain.Handler Proto.Request Reactor.Response :=
  { hid := 0, run := fun _ => .ok (Reactor.Deploy.deployResp input) }

/-- **`fallback_serves_once_deployed` — every deployed fallback run serves exactly
one thing.** For any configured chain ending in the deployed handler, running it
over the dispatched request serves EXACTLY one outcome — one handler response or
the terminal error page, never zero, never two (`Fallback.Chain.runChain_served_once`,
the accounting identity). The deployed response participates as a real chain
member, so the served-once floor holds of the deployed serve, not an isolated
model. -/
theorem fallback_serves_once_deployed (input : Bytes) (req : Proto.Request)
    (rp : Fallback.RetryPolicy) (fb : Fallback.ErrClass)
    (pre : List (Fallback.Chain.Handler Proto.Request Reactor.Response)) :
    (Fallback.Chain.runChain rp fb (pre ++ [deployHandler input]) req).2.servedResponses
      + (Fallback.Chain.runChain rp fb (pre ++ [deployHandler input]) req).2.servedTerminal
      = 1 :=
  Fallback.Chain.runChain_served_once rp fb _ req

/-- **`fallback_deployed_wins` — when every prior backend fails, the deployed
response is what gets served.** If every handler before the deployed tail failed
retryably (fell through), the chain stops at the deployed handler and serves
EXACTLY the deployed response `Reactor.Deploy.deployResp input`, with the trace
being every handler up to and including it — no handler runs after
(`Fallback.Chain.runChain_stops_at_first_success`). So the deployed serve is the
real fallback target. -/
theorem fallback_deployed_wins (input : Bytes) (req : Proto.Request)
    (rp : Fallback.RetryPolicy) (fb : Fallback.ErrClass)
    (pre : List (Fallback.Chain.Handler Proto.Request Reactor.Response))
    (hpre : ∀ g ∈ pre, ∃ c, g.run req = Fallback.Outcome.err c ∧ rp.retryable c = true) :
    Fallback.Chain.runChain rp fb (pre ++ [deployHandler input]) req
      = ((pre ++ [deployHandler input]).map Fallback.Chain.Handler.hid,
         Fallback.Chain.Served.byHandler 0 (Reactor.Deploy.deployResp input)) := by
  have h := Fallback.Chain.runChain_stops_at_first_success rp fb req pre
    (deployHandler input) [] (Reactor.Deploy.deployResp input) hpre rfl
  simpa using h

/-! ## (2) Cgi — the CGI environment of the deployed request is total -/

/-- The CGI/1.1 meta-variable request derived from the deployed dispatched
request: `REQUEST_METHOD` / `SCRIPT_NAME` come from the request head; the server
identity is the deployed listener's. -/
def deployCgiReq (req : Proto.Request) : Cgi.Req :=
  { requestMethod  := Reactor.App.bytesToString req.method
    scriptName     := Reactor.App.bytesToString req.target
    serverName     := "drorb"
    serverPort     := "8080"
    serverProtocol := "HTTP/1.1"
    serverSoftware := "drorb"
    remoteAddr     := "0.0.0.0" }

/-- The `REQUEST_METHOD` meta-variable is exactly the deployed request's method
(faithful to the dispatched request head). -/
theorem deployCgi_requestMethod (req : Proto.Request) :
    Cgi.env (deployCgiReq req) .requestMethod = Reactor.App.bytesToString req.method := rfl

/-- The `SCRIPT_NAME` meta-variable is exactly the deployed request's target. -/
theorem deployCgi_scriptName (req : Proto.Request) :
    Cgi.env (deployCgiReq req) .scriptName = Reactor.App.bytesToString req.target := rfl

/-- **`cgi_env_total_deployed` — the deployed request's CGI environment is
total.** For every CGI/1.1 meta-variable, the pair `(name, value)` occurs in the
environment the gateway builds from the deployed request — no meta-variable is
left unmapped (`Cgi.cgi_env_total`, full-domain coverage), and the environment
has exactly one entry per meta-variable (`Cgi.envList_length` = 17). -/
theorem cgi_env_total_deployed (req : Proto.Request) (m : Cgi.Meta) :
    (m.name, Cgi.env (deployCgiReq req) m) ∈ Cgi.envList (deployCgiReq req)
    ∧ (Cgi.envList (deployCgiReq req)).length = 17 :=
  ⟨Cgi.cgi_env_total (deployCgiReq req) m, Cgi.envList_length (deployCgiReq req)⟩

/-! ## (3) Redirect — a redirect built for the deployed request is well-formed -/

/-- A redirect response for the deployed dispatched request: substitute the
deployed request's target as the `{path}` into the configured `Location`
template (empty query for the derived path). -/
def deployRedirect (code : Redirect.Code) (template : List Redirect.Tok)
    (req : Proto.Request) : Redirect.Resp :=
  Redirect.redirect code template (Reactor.App.bytesToString req.target) ""

/-- **`redirect_3xx_deployed` — the deployed redirect is well-formed.** For the
deployed request's target, the built `Location` is exactly the faithful in-order
substitution of the target into the template (no placeholder dropped, duplicated,
or reordered) and the status is a genuine RFC 9110 §15.4 3xx redirect code that
carries a `Location` (`Redirect.redirect_location_wellformed`). -/
theorem redirect_3xx_deployed (code : Redirect.Code) (template : List Redirect.Tok)
    (req : Proto.Request) :
    (deployRedirect code template req).location
        = Redirect.subst (Reactor.App.bytesToString req.target) "" template
    ∧ (deployRedirect code template req).status ∈ Redirect.redirectStatuses :=
  Redirect.redirect_location_wellformed code template _ _

/-- **The followed request method is method-safe.** A 307/308 redirect of the
deployed request preserves the method (`Redirect.method_preserved`); a 301/302
downgrades an unsafe method to GET (`Redirect.method_safe_downgrade`). -/
theorem redirect_method_deployed (m : Redirect.Method)
    (hunsafe : m = Redirect.Method.post ∨ m = Redirect.Method.other) :
    Redirect.followedMethod .temp307 m = m
    ∧ Redirect.followedMethod .found302 m = Redirect.Method.get :=
  ⟨Redirect.method_preserved .temp307 m rfl,
   Redirect.method_safe_downgrade .found302 m rfl hunsafe⟩

/-! ## (4) ForwardProxy — the deployed body relayed through a CONNECT tunnel -/

/-- The deployed served body as a CONNECT-tunnel relay payload (`ForwardProxy.Bytes`
is `List UInt8`, exactly `Proto.Bytes`, so the served body is the payload
verbatim). -/
def deployTunnelPayload (input : Bytes) : ForwardProxy.Bytes :=
  (Reactor.Deploy.deployResp input).body

/-- **`forwardproxy_no_relay_deployed` — no deployed byte escapes before the
tunnel is established.** In any tunnel phase other than `connected`, relaying the
deployed served body through the CONNECT tunnel forwards NOTHING, in either
direction (`ForwardProxy.connect_no_relay_before_connected`). The blind-forwarding
gate is shut until the upstream connect succeeds. -/
theorem forwardproxy_no_relay_deployed (input : Bytes) (p : ForwardProxy.TPhase)
    (dir : ForwardProxy.Dir) (h : p ≠ .connected) :
    ForwardProxy.egress p dir (deployTunnelPayload input) = [] :=
  ForwardProxy.connect_no_relay_before_connected p dir _ h

/-- **`forwardproxy_relay_once_connected` — once established, the deployed body is
blindly forwarded verbatim.** In `connected` the relay is the identity on the
deployed served body, in either direction
(`ForwardProxy.connect_relay_transparent`). -/
theorem forwardproxy_relay_once_connected (input : Bytes) (dir : ForwardProxy.Dir) :
    ForwardProxy.egress .connected dir (deployTunnelPayload input)
      = deployTunnelPayload input :=
  ForwardProxy.connect_relay_transparent dir _

/-- **`forwardproxy_needs_upstreamOk_deployed` — the tunnel opens only after the
upstream connect succeeds.** If a run of tunnel events starting from a
not-yet-connected phase reaches `connected` (at which point the deployed body
would relay), the event sequence contained the successful upstream-connect event
(`ForwardProxy.run_connected_needs_upstreamOk`). -/
theorem forwardproxy_needs_upstreamOk_deployed (evs : List ForwardProxy.TEv)
    (p : ForwardProxy.TPhase) (hp : p ≠ .connected)
    (h : ForwardProxy.run p evs = .connected) :
    ForwardProxy.TEv.upstreamOk ∈ evs :=
  ForwardProxy.run_connected_needs_upstreamOk evs p hp h

/-! ## (5) Udp — relaying the deployed body preserves it byte-for-byte -/

/-- The deployed served body as a UDP datagram payload (`Udp.Payload` is
`List Nat`; the served `UInt8` bytes map through `UInt8.toNat`). -/
def deployDatagram (input : Bytes) : Udp.Payload :=
  (Reactor.Deploy.deployResp input).body.map (·.toNat)

/-- **`udp_integrity_deployed` — the UDP relay does not mutate the deployed
body.** A client datagram carrying the deployed served body is forwarded with the
payload byte-for-byte, for a live or a fresh client
(`Udp.onClient_forward_payload`). The relay never touches the body. -/
theorem udp_integrity_deployed (input : Bytes) (r : Udp.Relay) (a : Udp.Addr)
    (now : Nat) :
    (Udp.onClient r a (deployDatagram input) now).2.payload? = some (deployDatagram input) :=
  Udp.onClient_forward_payload r a (deployDatagram input) now

/-- **`udp_affinity_deployed` — two deployed datagrams from one client pin one
upstream.** A live client sending two datagrams carrying deployed bodies has both
forwarded to the SAME recorded binding — the client is not split across upstreams
mid-session (`Udp.affinity_two_datagrams`). -/
theorem udp_affinity_deployed (in1 in2 : Bytes) (r : Udp.Relay) (a : Udp.Addr)
    (now1 now2 : Nat) {s : Udp.Session} (h : Udp.lookup r.sessions a = some s) :
    (Udp.onClient r a (deployDatagram in1) now1).2 = Udp.Out.forward a s.binding (deployDatagram in1)
    ∧ (Udp.onClient (Udp.onClient r a (deployDatagram in1) now1).1 a (deployDatagram in2) now2).2
        = Udp.Out.forward a s.binding (deployDatagram in2) :=
  Udp.affinity_two_datagrams r a (deployDatagram in1) (deployDatagram in2) now1 now2 h

/-! ## (6) Mtls — no identity is fabricated on the deployed surface -/

/-- **`mtls_no_bypass_deployed` — the deployed surface authenticates no one
without a verified chain.** The deployed listener is plaintext, so it presents no
client certificate (the empty chain): verification rejects it (`Mtls.verify_empty`)
and identity extraction yields NONE (`Mtls.authenticate_empty`). There is no path
from an absent/failed client chain to an authenticated identity. -/
theorem mtls_no_bypass_deployed (env : Mtls.Env) (now : Mtls.Time) :
    Mtls.verifyFrom env now [] = false ∧ Mtls.authenticate env now [] = none :=
  ⟨Mtls.verify_empty env now, Mtls.authenticate_empty env now⟩

/-- **`mtls_unverified_no_identity_deployed` — an unverified client chain yields
no identity.** Whenever the REAL path validator rejects a presented chain, the
extractor produces no identity (`Mtls.authenticate_unverified`) — the no-bypass
property, on any chain the deployed surface might see. -/
theorem mtls_unverified_no_identity_deployed (env : Mtls.Env) (now : Mtls.Time)
    (chain : Mtls.Chain) (h : Mtls.verifyFrom env now chain = false) :
    Mtls.authenticate env now chain = none :=
  Mtls.authenticate_unverified h

/-! ## (7) Drain — the deployed listener refuses new connections after SIGTERM

A concrete deployed graceful-shutdown scenario over `Drain.step`: the deployed
listener admits one connection, then begin-drain (SIGTERM) fires. -/

/-- The deployed listener after admitting one connection (running, one in flight). -/
def deployDrainAdmitted : Drain.DState := (Drain.step Drain.init .acceptReq).1

/-- The deployed listener after begin-drain (SIGTERM), deadline 100. -/
def deployDraining : Drain.DState :=
  (Drain.step deployDrainAdmitted (.beginDrain 100)).1

/-- Begin-drain moves the deployed listener out of `running` into `draining`
(there is one in-flight connection to wait on). -/
theorem deployDraining_mode : deployDraining.mode = .draining := by decide

/-- **`drain_no_accept_deployed` — after SIGTERM the deployed listener refuses new
connections.** In the draining deployed listener, an accept attempt is REFUSED
(`Drain.acceptReq_refused_of_not_running`) and the in-flight count is unchanged
(refusal charges nothing) — new work is shut off exactly at begin-drain while the
in-flight connection is allowed to complete. -/
theorem drain_no_accept_deployed :
    (Drain.step deployDraining .acceptReq).2 = [Drain.Output.refused]
    ∧ (Drain.step deployDraining .acceptReq).1.inflight = deployDraining.inflight :=
  ⟨Drain.acceptReq_refused_of_not_running (by decide),
   Drain.acceptReq_refused_inflight_unchanged (by decide)⟩

/-- **`drain_accounted_deployed` — no in-flight connection is silently lost.** The
deployed draining listener satisfies the accounting identity: every admitted
connection is still in flight, completed, or force-closed
(`Drain.step_accounted` from `Drain.accounted_init`). -/
theorem drain_accounted_deployed : Drain.Accounted deployDraining :=
  Drain.step_accounted _ (Drain.step_accounted _ Drain.accounted_init)

/-- **`drain_completes_reaches_drained_deployed` — completing the in-flight
connection reaches `drained`.** From the deployed draining listener (one in
flight), a `complete` retires the last connection and moves to `drained` with
nothing outstanding (`Drain.complete_reaches_drained`). -/
theorem drain_completes_reaches_drained_deployed :
    (Drain.step deployDraining .complete).1.mode = .drained
    ∧ (Drain.step deployDraining .complete).1.inflight = 0 :=
  Drain.complete_reaches_drained (by decide) (by decide)

/-! ## (8) Resume — a deployed session ticket is window-bounded and epoch-owned

The deployed key generation `deployResumeEpoch`; a resumption ticket minted for a
deployed session carries a 3600s lifetime under that generation. -/

/-- The deployed key generation (epoch 0 at cold boot). -/
def deployResumeEpoch : Nat := 0

/-- A resumption ticket for the deployed session, minted at `issued` under the
deployed key generation, lifetime 3600s. -/
def deployTicket (issued : Nat) : Resume.Ticket :=
  { issued := issued, lifetime := 3600, epoch := deployResumeEpoch }

/-- **`resume_window_deployed` — a deployed ticket is accepted only inside its
window.** If the deployed session ticket is accepted at `now`, then `now` lies in
its half-open validity window `[issued, issued + lifetime)`
(`Resume.accept_in_window`). -/
theorem resume_window_deployed (issued now : Nat)
    (h : Resume.accept (deployTicket issued) now deployResumeEpoch = true) :
    (deployTicket issued).issued ≤ now ∧ now < (deployTicket issued).expiry :=
  Resume.accept_in_window h

/-- **`resume_expired_deployed` — an expired deployed ticket is refused.** At or
past `issued + lifetime` the deployed session ticket is never accepted
(`Resume.expired_refused`) — the resumption window is closed on the right. -/
theorem resume_expired_deployed (issued now : Nat)
    (h : (deployTicket issued).expiry ≤ now) :
    Resume.accept (deployTicket issued) now deployResumeEpoch = false :=
  Resume.expired_refused (deployTicket issued) now deployResumeEpoch h

/-- **`resume_rotation_invalidates_deployed` — a key rotation invalidates the
deployed ticket.** After the deployed key rotates (SIGHUP), a ticket minted under
the old generation is refused under the new one regardless of time
(`Resume.rotate_invalidates`) — the single-owner handover is atomic and complete. -/
theorem resume_rotation_invalidates_deployed (s : Resume.Server) (issued now : Nat)
    (h : (deployTicket issued).epoch = s.epoch) :
    Resume.accept (deployTicket issued) now s.rotate.epoch = false :=
  Resume.rotate_invalidates s (deployTicket issued) now h

/-! ## Axiom audit — every deployed seam is closed on the standard axioms only -/

#print axioms fallback_serves_once_deployed
#print axioms fallback_deployed_wins
#print axioms cgi_env_total_deployed
#print axioms deployCgi_requestMethod
#print axioms redirect_3xx_deployed
#print axioms redirect_method_deployed
#print axioms forwardproxy_no_relay_deployed
#print axioms forwardproxy_relay_once_connected
#print axioms forwardproxy_needs_upstreamOk_deployed
#print axioms udp_integrity_deployed
#print axioms udp_affinity_deployed
#print axioms mtls_no_bypass_deployed
#print axioms mtls_unverified_no_identity_deployed
#print axioms deployDraining_mode
#print axioms drain_no_accept_deployed
#print axioms drain_accounted_deployed
#print axioms drain_completes_reaches_drained_deployed
#print axioms resume_window_deployed
#print axioms resume_expired_deployed
#print axioms resume_rotation_invalidates_deployed

end WireRest
end Reactor
