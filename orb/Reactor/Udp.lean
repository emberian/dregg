import Reactor.Contract
import Reactor.Config
import Reactor.Bridge
import Udp.Session
import Udp.Correlation

/-!
# Reactor.Udp — wiring the real UDP session relay into the reactor's submission stream

The `Udp` library is a proven L4 datagram relay: a per-client session table
(key-unique, binding-injective, allocator-dominated — `Udp.Relay.Inv`) whose
three transitions (`onClient`, `onUpstream`, `sweep`) carry session affinity
(`binding_stable_onClient`, `affinity_run`), payload integrity
(`onClient_forward_payload`), reply correlation (`reply_routes_to_owner`), and
deadline-honored eviction. Until now nothing connected those transitions to the
reactor: the relay's `Udp.Out` decisions never became ring submissions, so the
proven affinity had no wire to ride.

This file closes that gap. The wiring, outside-in:

  * `payloadOf` — a datagram's wire bytes (`Proto.Bytes`, what the ring hands
    us) viewed as the relay's payload (`UInt8.toNat` per byte; the relay treats
    the payload as opaque and never mutates it).
  * `subOfOut` — the faithful translation of the relay's decision into the
    reactor's submission language (`Reactor.RingSubmission`, the same stream
    `Reactor.step` emits into): `forward _ u _` becomes
    `submitSendUpstream u data` — the datagram goes out on the per-session
    upstream binding `u` the REAL relay chose — `deliver _ _` becomes
    `submitSend data` (back toward the client; the addressee is named by the
    library's `Out.deliver`, see `onReply_names_owner`), and `drop` submits
    nothing. The submission carries the ORIGINAL wire bytes verbatim — the
    routing decision is the library's, byte custody never leaves the reactor.
  * `onDatagram` / `onReply` — one datagram (client → upstream) / one reply
    (upstream → client) step: run the REAL `Udp.onClient` / `Udp.onUpstream`
    and translate its output. The next relay state is the library's, unchanged.
  * `OrbState` / `orbStep` — the composition with the reactor: one machine
    holding the connection FSM state and the relay side by side. A ring event
    is handled by the REAL `Reactor.step` at the config passed in; a
    datagram/reply/sweep event by the real relay; both lanes emit into the
    single shared `RingSubmission` stream. `main` runs `serveFull` over
    `Reactor.Deploy.deployConfig`; on the plainH1 recv path the ring lane at
    `deployConfig` equals the test reactor's `Reactor.reactorSubs`
    (`orb_ring_deployed_eq_test`, the Bridge congruence), so the island seams
    proven over the test reactor cover the composed orb's ring lane on the
    deployed path too.

## The seam theorem

`udp_session_affinity_seam` — over `orbStep` (config-polymorphic in the ring
lane, restated at the deployed `Reactor.Deploy.deployConfig` as
`udp_session_affinity_seam_deployed`): if the real `Udp` session table holds
upstream binding `u` for client `a` (`Udp.bindingOf … = some u`), then

  1. a datagram from `a` is submitted as exactly
     `[submitSendUpstream u data]` — routed to the very binding the real
     session table holds, payload verbatim; and
  2. after ANY eviction-free schedule of further orb events (more datagrams
     from any client, upstream replies, ring events through the deployed
     reactor step), a datagram from `a` STILL routes to the same `u` — the
     session is never re-pinned mid-life (`orb_affinity_run`, lifting the
     library's `binding_stable_onClient` / `binding_stable_onUpstream`).

A stub that re-chose the upstream per datagram (round-robin over datagrams,
say) would violate (2); one that ignored the table would violate (1) — the
emitted `u` is *defined* to be the binding the real `Udp.onClient` read from
its session table.

Composition hygiene with the copy-once reactor contract:
`orb_ring_is_reactor` (the ring lane IS `Reactor.step`, untouched),
`orb_recv_recycles_exactly_once` (the reactor's recycle accounting survives the
composition), and `orb_datagram_no_recycle` (the datagram lane never forges a
buffer recycle).

Honest scope note: the deployed `main` is a single-request HTTP view over
`serveFull` (the proven reactor over `Reactor.Deploy.deployConfig`); it has no
datagram ingress. The UDP lane is wired into the reactor's own submission
language and composed with the deployed reactor step (`Reactor.step`, driven at
`deployConfig` in `udp_session_affinity_seam_deployed`) in `orbStep` — the IO
shell that feeds datagram completions alongside recv completions is environment,
per the assurance boundary.
-/

namespace Reactor.UdpWire

open Proto (Bytes)

/-! ## Bytes ↔ relay payload -/

/-- A datagram's wire bytes as the relay's payload (`Udp.Payload := List Nat`).
The relay treats the payload as opaque — this view is only what lets the real
`Udp` transitions be driven by ring bytes. -/
def payloadOf (b : Bytes) : Udp.Payload := b.map (fun x => x.toNat)

/-! ## The faithful translation: relay decision → ring submission -/

/-- Translate the REAL relay's forwarding decision into the reactor's
submission language, carrying the original wire bytes `data` verbatim:

  * `forward _ u _` → `submitSendUpstream u data`: the datagram goes out on the
    per-session upstream binding `u` the relay chose;
  * `deliver _ _` → `submitSend data`: the reply goes back toward the client
    (the addressee is the library's `Out.deliver` client — see
    `onReply_names_owner`);
  * `drop` → no submission (a reply with no live session is not forwarded).

The `u` in the emitted submission is read from the relay's `Out` — the routing
decision is the library's, never re-made here. -/
def subOfOut (data : Bytes) : Udp.Out → List RingSubmission
  | .forward _ u _ => [RingSubmission.submitSendUpstream u data]
  | .deliver _ _   => [RingSubmission.submitSend data]
  | .drop          => []

/-- One client datagram: run the REAL `Udp.onClient` on the relay state and
translate its decision. The next relay state is the library's own. -/
def onDatagram (r : Udp.Relay) (a : Udp.Addr) (data : Bytes) (now : Nat) :
    Udp.Relay × List RingSubmission :=
  ((Udp.onClient r a (payloadOf data) now).1,
   subOfOut data (Udp.onClient r a (payloadOf data) now).2)

/-- One upstream reply on binding `u`: run the REAL `Udp.onUpstream` and
translate its decision. -/
def onReply (r : Udp.Relay) (u : Nat) (data : Bytes) (now : Nat) :
    Udp.Relay × List RingSubmission :=
  ((Udp.onUpstream r u (payloadOf data) now).1,
   subOfOut data (Udp.onUpstream r u (payloadOf data) now).2)

/-! ## Step-level routing facts (the library decides, the submission records) -/

/-- **A live client's datagram is submitted to its recorded binding.** When the
real session table has session `s` for client `a`, the emitted submission is
exactly `submitSendUpstream s.binding data` — the binding is read from the
table (`Udp.onClient_existing_forward`), never re-chosen, and the wire bytes
ride verbatim. -/
theorem onDatagram_live {r : Udp.Relay} {a : Udp.Addr} {s : Udp.Session}
    (data : Bytes) (now : Nat) (h : Udp.lookup r.sessions a = some s) :
    (onDatagram r a data now).2
      = [RingSubmission.submitSendUpstream s.binding data] := by
  show subOfOut data (Udp.onClient r a (payloadOf data) now).2 = _
  rw [Udp.onClient_existing_forward h]
  rfl

/-- **A fresh client's datagram opens a session on the freshly allocated
binding** (`nextBinding`, allocator-dominance making it distinct from every
live binding). -/
theorem onDatagram_fresh {r : Udp.Relay} {a : Udp.Addr}
    (data : Bytes) (now : Nat) (h : Udp.lookup r.sessions a = none) :
    (onDatagram r a data now).2
      = [RingSubmission.submitSendUpstream r.nextBinding data] := by
  show subOfOut data (Udp.onClient r a (payloadOf data) now).2 = _
  rw [Udp.onClient_fresh_forward h]
  rfl

/-- **Routes to the held binding.** Stated against `Udp.bindingOf` — the
binding the real session table currently holds for `a` is the `fd` of the
emitted upstream submission. -/
theorem udp_routes_to_held_binding {r : Udp.Relay} {a : Udp.Addr} {u : Nat}
    (data : Bytes) (now : Nat) (h : Udp.bindingOf r.sessions a = some u) :
    (onDatagram r a data now).2
      = [RingSubmission.submitSendUpstream u data] := by
  unfold Udp.bindingOf at h
  cases hl : Udp.lookup r.sessions a with
  | none => rw [hl] at h; simp at h
  | some s =>
    rw [hl] at h
    have hb : s.binding = u := by simpa using h
    rw [onDatagram_live data now hl, hb]

/-- A datagram (from any client) leaves every held binding held: the wired step
inherits the library's `binding_stable_onClient`. -/
theorem onDatagram_binding_stable (r : Udp.Relay) (a b : Udp.Addr)
    (data : Bytes) (now : Nat) {u : Nat}
    (hb : Udp.bindingOf r.sessions b = some u) :
    Udp.bindingOf (onDatagram r a data now).1.sessions b = some u :=
  Udp.binding_stable_onClient r a b (payloadOf data) now hb

/-- **Payload integrity, witnessed by the library.** The relay's own output for
a datagram carries the (viewed) payload byte-for-byte
(`Udp.onClient_forward_payload`); the emitted submission carries the original
wire bytes by construction (`subOfOut` re-emits `data` itself). -/
theorem onDatagram_payload_verbatim (r : Udp.Relay) (a : Udp.Addr)
    (data : Bytes) (now : Nat) :
    (Udp.onClient r a (payloadOf data) now).2.payload? = some (payloadOf data) :=
  Udp.onClient_forward_payload r a (payloadOf data) now

/-- **A reply is delivered to the binding's owner — named by the real library.**
The `Udp.onUpstream` output for a reply on a live session's binding is
`deliver a _` for exactly the owning client `a`
(`Udp.reply_routes_to_owner`, unique by binding-injectivity). -/
theorem onReply_names_owner {r : Udp.Relay} {a : Udp.Addr} {s : Udp.Session}
    {u : Nat} (data : Bytes) (now : Nat) (hinv : r.Inv)
    (h : Udp.lookup r.sessions a = some s) (hu : s.binding = u) :
    (Udp.onUpstream r u (payloadOf data) now).2
      = Udp.Out.deliver a (payloadOf data) :=
  Udp.reply_routes_to_owner hinv h hu

/-- A reply on a live binding is submitted back toward the client, bytes
verbatim; a reply on a dead binding submits nothing (`Out.drop` → `[]`). -/
theorem onReply_live {r : Udp.Relay} {a : Udp.Addr} {s : Udp.Session} {u : Nat}
    (data : Bytes) (now : Nat) (hinv : r.Inv)
    (h : Udp.lookup r.sessions a = some s) (hu : s.binding = u) :
    (onReply r u data now).2 = [RingSubmission.submitSend data] := by
  show subOfOut data (Udp.onUpstream r u (payloadOf data) now).2 = _
  rw [onReply_names_owner data now hinv h hu]
  rfl

/-! ## The composition with the reactor -/

/-- The composed machine's state: the connection FSM state the deployed
`Reactor.step` drives, and the real `Udp` relay, side by side. -/
structure OrbState where
  conn : Proto.State
  relay : Udp.Relay

/-- The composed machine's events: a ring completion (the deployed reactor
lane) or a datagram-lane event (client datagram, upstream reply, idle sweep).
Time enters the datagram lane only through the explicit `now` fields, exactly
as in the library. -/
inductive OrbEvent where
  | ring (e : RingEvent)
  | datagram (a : Udp.Addr) (data : Bytes) (now : Nat)
  | reply (u : Nat) (data : Bytes) (now : Nat)
  | sweep (now : Nat)

/-- Is this the eviction event? Ring/datagram/reply events never evict. -/
def OrbEvent.isSweep : OrbEvent → Bool
  | .sweep _ => true
  | _ => false

/-- **The composed step.** A ring event runs the REAL `Reactor.step` at the
config passed in (at `Reactor.Deploy.deployConfig` this is the reactor step
`serveFull`/`main` run); a datagram/reply/sweep event runs the REAL `Udp`
transition. Both lanes emit into the one shared submission stream. -/
def orbStep (cfg : Proto.Config) (timeout : Nat) (s : OrbState) :
    OrbEvent → OrbState × List RingSubmission
  | .ring e =>
    ({ conn := (Reactor.step cfg s.conn e).1, relay := s.relay },
     (Reactor.step cfg s.conn e).2)
  | .datagram a data now =>
    ({ conn := s.conn, relay := (onDatagram s.relay a data now).1 },
     (onDatagram s.relay a data now).2)
  | .reply u data now =>
    ({ conn := s.conn, relay := (onReply s.relay u data now).1 },
     (onReply s.relay u data now).2)
  | .sweep now =>
    ({ conn := s.conn, relay := Udp.sweep timeout now s.relay }, [])

/-- Run a whole schedule of composed events. -/
def orbRun (cfg : Proto.Config) (timeout : Nat) (s : OrbState) :
    List OrbEvent → OrbState
  | [] => s
  | e :: es => orbRun cfg timeout (orbStep cfg timeout s e).1 es

/-- **The ring lane IS the deployed reactor.** On a ring event the composed
step's submissions are exactly `Reactor.step`'s — the composition adds nothing
to and removes nothing from the deployed path. -/
theorem orb_ring_is_reactor (cfg : Proto.Config) (timeout : Nat) (s : OrbState)
    (e : RingEvent) :
    (orbStep cfg timeout s (.ring e)).2 = (Reactor.step cfg s.conn e).2 := rfl

/-- A ring event leaves the relay untouched; a datagram-lane event leaves the
connection FSM untouched. The lanes do not interfere. -/
theorem orb_lanes_independent (cfg : Proto.Config) (timeout : Nat) (s : OrbState)
    (e : RingEvent) (a : Udp.Addr) (data : Bytes) (now : Nat) :
    (orbStep cfg timeout s (.ring e)).1.relay = s.relay
    ∧ (orbStep cfg timeout s (.datagram a data now)).1.conn = s.conn :=
  ⟨rfl, rfl⟩

/-! ## Copy-once hygiene: the datagram lane forges no recycle -/

/-- The datagram-lane translation never emits a buffer recycle. -/
theorem subOfOut_no_recycle (data : Bytes) (o : Udp.Out) :
    (subOfOut data o).filter RingSubmission.isRecycle = [] := by
  cases o <;> rfl

/-- A datagram event contributes no recycle submission — the reactor's
copy-once accounting cannot be confused by the UDP lane. -/
theorem orb_datagram_no_recycle (cfg : Proto.Config) (timeout : Nat)
    (s : OrbState) (a : Udp.Addr) (data : Bytes) (now : Nat) :
    ((orbStep cfg timeout s (.datagram a data now)).2.filter
        RingSubmission.isRecycle) = [] :=
  subOfOut_no_recycle data _

/-- **Recycle-exactly-once survives the composition.** A recv completion
through the composed step still yields exactly one recycle, of that buffer —
the deployed reactor's `recv_recycles_exactly_once`, verbatim. -/
theorem orb_recv_recycles_exactly_once (cfg : Proto.Config) (timeout : Nat)
    (s : OrbState) (bid : Uring.Bid) (data : Bytes) :
    ((orbStep cfg timeout s (.ring (.recvInto bid data))).2.filter
        RingSubmission.isRecycle)
      = [RingSubmission.recycleBuffer bid] :=
  Reactor.recv_recycles_exactly_once cfg s.conn bid data

/-! ## Relay invariant and affinity, over composed schedules -/

/-- Every composed step preserves the relay invariant (ring events don't touch
the relay; datagram-lane events are the library's invariant-preserving
transitions). -/
theorem orbStep_relay_inv (cfg : Proto.Config) (timeout : Nat) (s : OrbState)
    (e : OrbEvent) (hinv : s.relay.Inv) :
    (orbStep cfg timeout s e).1.relay.Inv := by
  cases e with
  | ring e' => exact hinv
  | datagram a data now => exact Udp.onClient_inv hinv
  | reply u data now => exact Udp.onUpstream_inv hinv
  | sweep now => exact Udp.sweep_inv hinv

/-- The relay invariant survives every composed schedule. -/
theorem orbRun_relay_inv (cfg : Proto.Config) (timeout : Nat) (s : OrbState)
    (es : List OrbEvent) (hinv : s.relay.Inv) :
    (orbRun cfg timeout s es).relay.Inv := by
  induction es generalizing s with
  | nil => exact hinv
  | cons e es ih => exact ih _ (orbStep_relay_inv cfg timeout s e hinv)

/-- **Affinity across a composed schedule.** Over any eviction-free schedule of
composed events — datagrams from any client, upstream replies, ring events
through the deployed reactor — a held binding stays held: the client is never
re-pinned mid-session. Lifts the library's `binding_stable_onClient` /
`binding_stable_onUpstream` through the composition. -/
theorem orb_affinity_run (cfg : Proto.Config) (timeout : Nat) (s : OrbState)
    (es : List OrbEvent) (hns : ∀ e ∈ es, e.isSweep = false)
    (hinv : s.relay.Inv) {b : Udp.Addr} {u : Nat}
    (hb : Udp.bindingOf s.relay.sessions b = some u) :
    Udp.bindingOf (orbRun cfg timeout s es).relay.sessions b = some u := by
  induction es generalizing s with
  | nil => exact hb
  | cons e es ih =>
    have hns_e : e.isSweep = false := hns e (List.mem_cons_self _ _)
    have hstep : Udp.bindingOf (orbStep cfg timeout s e).1.relay.sessions b
        = some u := by
      cases e with
      | ring e' => exact hb
      | datagram a data now =>
        exact Udp.binding_stable_onClient s.relay a b (payloadOf data) now hb
      | reply v data now => exact Udp.binding_stable_onUpstream hinv hb
      | sweep now => simp [OrbEvent.isSweep] at hns_e
    exact ih (orbStep cfg timeout s e).1
      (fun e' he' => hns e' (List.mem_cons_of_mem _ he'))
      (orbStep_relay_inv cfg timeout s e hinv) hstep

/-! ## The seam theorem -/

/-- **`udp_session_affinity_seam` — session affinity, composed with the
deployed reactor.** Over `orbStep` at `Reactor.Config.demoConfig` (the config
the island seams were proven over; the deployed variant at `deployConfig` is
`udp_session_affinity_seam_deployed`): if the REAL `Udp` session table holds
upstream binding `u` for client `a`, then

  1. a datagram from `a` is submitted as exactly
     `[submitSendUpstream u data]` — the same upstream binding the real
     session table holds, wire bytes verbatim; and
  2. after ANY eviction-free schedule of further composed events (datagrams,
     replies, ring events through the deployed reactor step), a datagram from
     `a` still routes to that same `u`.

The emitted binding is *defined* to be the one `Udp.onClient` reads from its
table, so a wiring that re-chose upstreams per datagram or ignored the table
cannot satisfy this. -/
theorem udp_session_affinity_seam (timeout : Nat) (s : OrbState)
    (a : Udp.Addr) (u : Nat) (data : Bytes) (now : Nat)
    (hinv : s.relay.Inv)
    (hheld : Udp.bindingOf s.relay.sessions a = some u) :
    (orbStep Reactor.Config.demoConfig timeout s (.datagram a data now)).2
        = [RingSubmission.submitSendUpstream u data]
    ∧ ∀ (es : List OrbEvent), (∀ e ∈ es, e.isSweep = false) →
        ∀ (data' : Bytes) (now' : Nat),
          (orbStep Reactor.Config.demoConfig timeout
              (orbRun Reactor.Config.demoConfig timeout s es)
              (.datagram a data' now')).2
            = [RingSubmission.submitSendUpstream u data'] := by
  constructor
  · show (onDatagram s.relay a data now).2 = _
    exact udp_routes_to_held_binding data now hheld
  · intro es hns data' now'
    have hb' := orb_affinity_run Reactor.Config.demoConfig timeout s es hns
      hinv hheld
    show (onDatagram (orbRun Reactor.Config.demoConfig timeout s es).relay
        a data' now').2 = _
    exact udp_routes_to_held_binding data' now' hb'

/-! ## Deployed-path corollaries — the seam on the config `main` runs -/

/-- **The ring lane on the deployed path IS the test reactor.** On a fresh plain
connection receiving `input`, the composed step's ring-lane submissions at
`Reactor.Deploy.deployConfig` (the config `main`/`serveFull` runs) are exactly
`Reactor.reactorSubs input` — the submissions the island seams were proven over.
`orb_ring_is_reactor` unfolds the ring lane to `Reactor.step`; the Bridge
congruence (`deploySubs_eq_reactorSubs`) closes the deployConfig↔demoConfig gap
on the plainH1 arm. So every `reactorSubs`/`serve` island seam holds of the
composed orb's ring lane on the deployed path. -/
theorem orb_ring_deployed_eq_test (timeout : Nat) (relay : Udp.Relay)
    (input : Bytes) :
    (orbStep Reactor.Deploy.deployConfig timeout
        ⟨Proto.State.active Proto.Conn.mkPlain, relay⟩
        (.ring (.recvInto 0 input))).2
      = Reactor.reactorSubs input := by
  rw [orb_ring_is_reactor]
  exact Reactor.Bridge.deploySubs_eq_reactorSubs input

/-- **`udp_session_affinity_seam_deployed` — the affinity seam at the config
`main` runs.** Identical to `udp_session_affinity_seam` but over `orbStep` /
`orbRun` at `Reactor.Deploy.deployConfig`, the config the deployed orb executes
(`serveFull`/`deployStep`). The datagram lane's submission is a pure function of
the real relay's decision (`onDatagram`), independent of the reactor config, and
the relay evolution under `orbRun` is untouched by ring events at any config
(`orb_affinity_run` is config-polymorphic), so the seam lands verbatim on the
deployed config. -/
theorem udp_session_affinity_seam_deployed (timeout : Nat) (s : OrbState)
    (a : Udp.Addr) (u : Nat) (data : Bytes) (now : Nat)
    (hinv : s.relay.Inv)
    (hheld : Udp.bindingOf s.relay.sessions a = some u) :
    (orbStep Reactor.Deploy.deployConfig timeout s (.datagram a data now)).2
        = [RingSubmission.submitSendUpstream u data]
    ∧ ∀ (es : List OrbEvent), (∀ e ∈ es, e.isSweep = false) →
        ∀ (data' : Bytes) (now' : Nat),
          (orbStep Reactor.Deploy.deployConfig timeout
              (orbRun Reactor.Deploy.deployConfig timeout s es)
              (.datagram a data' now')).2
            = [RingSubmission.submitSendUpstream u data'] := by
  constructor
  · show (onDatagram s.relay a data now).2 = _
    exact udp_routes_to_held_binding data now hheld
  · intro es hns data' now'
    have hb' := orb_affinity_run Reactor.Deploy.deployConfig timeout s es hns
      hinv hheld
    show (onDatagram (orbRun Reactor.Deploy.deployConfig timeout s es).relay
        a data' now').2 = _
    exact udp_routes_to_held_binding data' now' hb'

/-! ## Concrete data: a real relay state, driven and routed -/

/-- A relay reached by running the REAL `Udp.run` on two client datagrams
(clients `1` and `2` at time `0`, idle timeout `30`): client `1` is pinned to
binding `0`, client `2` to binding `1`. -/
def demoRelay : Udp.Relay :=
  Udp.run 30 Udp.Relay.init [.client 1 [] 0, .client 2 [] 0]

/-- `demoRelay` satisfies the relay invariant — by the library's `run_init_inv`,
not by fiat. -/
theorem demoRelay_inv : demoRelay.Inv := Udp.run_init_inv 30 _

theorem demoRelay_client1 : Udp.bindingOf demoRelay.sessions 1 = some 0 := by
  decide

theorem demoRelay_client2 : Udp.bindingOf demoRelay.sessions 2 = some 1 := by
  decide

theorem demoRelay_lookup1 : Udp.lookup demoRelay.sessions 1 = some ⟨0, 0⟩ := by
  decide

/-- The composed demo state: the deployed reactor's initial connection state
next to the driven relay. -/
def demoOrb : OrbState :=
  { conn := Proto.State.active Proto.Conn.mkPlain, relay := demoRelay }

/-- **The wiring on concrete data.** Through the composed step at the deployed
config, every datagram from client `1` is submitted on upstream binding `0` —
the binding the real session table holds — whatever the payload and time. -/
theorem demo_datagram_routes (data : Bytes) (now : Nat) :
    (orbStep Reactor.Config.demoConfig 30 demoOrb (.datagram 1 data now)).2
      = [RingSubmission.submitSendUpstream 0 data] :=
  udp_routes_to_held_binding data now demoRelay_client1

/-- **Reply correlation on concrete data.** A reply on binding `0` is submitted
back toward the client, and the real library names the addressee: client `1`,
the binding's unique owner. -/
theorem demo_reply_routes (data : Bytes) (now : Nat) :
    (orbStep Reactor.Config.demoConfig 30 demoOrb (.reply 0 data now)).2
      = [RingSubmission.submitSend data] :=
  onReply_live data now demoRelay_inv demoRelay_lookup1 rfl

/-- The library's naming of the demo reply's addressee (client `1`). -/
theorem demo_reply_owner (data : Bytes) (now : Nat) :
    (Udp.onUpstream demoRelay 0 (payloadOf data) now).2
      = Udp.Out.deliver 1 (payloadOf data) :=
  onReply_names_owner data now demoRelay_inv demoRelay_lookup1 rfl

end Reactor.UdpWire
