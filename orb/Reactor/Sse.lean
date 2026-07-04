import Reactor.ProxyServe
import Reactor.Serve
import Reactor.Bridge
import Sse.Broadcast
import Sse.Frame

/-!
# Reactor.Sse — event-stream fan-out on the running reactor path

The real `Sse` library owns the broadcaster: a trace of operations
(`subscribe` / `unsubscribe` / `publish`) determines a monotone published
stream (`Sse.published`, sequence-tagged) and, per subscriber, the delivery log
(`Sse.delivered`) with the proven fan-out accounting — soundness
(`delivered_sublist_published`), order (`delivered_pairwise`), completeness
while subscribed (`delivered_split`), and silence after unsubscribe
(`deliveredAux_silent`). This file wires that broadcaster into the reactor:

  * `eventBytes` — the wire bytes of one dispatched event: the REAL
    `Sse.encodeFrame` (the frame whose parse round-trip is
    `Sse.parseFrame_encodeFrame`), each line closed with the transport `LF`.
  * `subscribeOnDispatch` — a connection becomes a subscriber through the
    reactor's own `dispatch` submission: the request that flowed through the
    PROVEN `Reactor.step` opens the subscription. Same seam `Reactor.Serve`
    answers with a Response.
  * `sseSession` — the broadcaster trace of one reactor-driven session: the
    reactor-produced subscribe, then the broadcast operations that follow.
  * `fanOut` / `sseServe` — the reactor's delivery: one `submitSend` of the
    encoded event per entry of the REAL `Sse.delivered` log, in log order. The
    reactor forwards the broadcaster's verdict; it does not reimplement the
    subscriber-set/sequence bookkeeping.

**Seam theorem — `sse_fanout_seam`.** The submissions the reactor delivers to a
subscriber are exactly the image of the real broadcaster's delivery log, and
that log is an order-preserving subsequence of the global published stream with
strictly increasing sequence tags: only real events, in publish order, no
duplicates. **`sse_no_gap`** is the completeness half on the running path: once
the reactor's `dispatch` opens the subscription and the client is never
unsubscribed, the reactor sends *every* published event, in order — the
delivered stream IS the published stream. **`sse_no_dispatch_silent`**: no
dispatch (the reactor refused the request bytes), no re-subscribe ⇒ nothing is
ever sent. A fan-out that dropped, reordered, or duplicated an event would
break `sse_no_gap`/the sublist conjunct; one that invented deliveries for an
unsubscribed connection would break silence.

The demo instantiates the seam at `Config.demoConfig` (the config the test view
`serve` runs): a reactor-dispatched subscribe followed by two publishes delivers
exactly those two encoded frames, in order. `Arena.Orb.main` runs
`Reactor.Deploy.serveFull` over `deployConfig`, whose reactor produces the same
submissions (`Reactor.Bridge.deploySubs_eq_reactorSubs`); `sse_fanout_deployed`
states the fan-out over `Reactor.Deploy.deploySubs`, the config `main` serves.
-/

namespace Reactor.Sse

open Proto (Bytes Request)

/-! ## Event wire bytes -/

/-- The wire bytes of one dispatched event: the REAL `Sse.encodeFrame` — the
field lines in canonical order, then the blank dispatch line — with each line
closed by the transport `LF`. The byte-level parse of this frame is proven to
recover the event (`Sse.parseFrame_encodeFrame`, for `Sse.Event.Wf` events). -/
def eventBytes (e : Sse.Event) : Bytes :=
  ((Sse.encodeFrame e).map (fun l => l ++ [Sse.LF])).flatten

/-- One delivery, as the reactor's own submission: send the encoded event on
the subscriber's connection. The sequence tag rides along in the log; the wire
carries the frame (`id:` inside the frame is the resumption layer's concern). -/
def submissionOf (p : Nat × Sse.Event) : RingSubmission :=
  RingSubmission.submitSend (eventBytes p.2)

/-! ## Subscribing through the reactor's dispatch -/

/-- A connection becomes a subscriber through the reactor's own `dispatch`
submission: scan the running reactor's submission list; the dispatched request
opens `c`'s subscription. No dispatch (the FSM refused or the request is
incomplete) ⇒ no subscription. -/
def subscribeOnDispatch (c : Sse.SubId) : List RingSubmission → List Sse.Op
  | [] => []
  | RingSubmission.dispatch _ :: _ => [Sse.Op.subscribe c]
  | _ :: rest => subscribeOnDispatch c rest

/-- The broadcaster trace of one reactor-driven session: the subscribe produced
by running the PROVEN `Reactor.step` on the input bytes
(`ProxyServe.reactorSubs`), then the broadcast operations that follow. -/
def sseSession (cfg : Proto.Config) (c : Sse.SubId) (input : Bytes)
    (ops : List Sse.Op) : List Sse.Op :=
  subscribeOnDispatch c (ProxyServe.reactorSubs cfg input) ++ ops

/-- **The reactor fan-out.** One `submitSend` of the encoded event per entry of
the REAL `Sse.delivered` log, in log order — the reactor forwards the
broadcaster's delivery verdict unchanged. -/
def fanOut (c : Sse.SubId) (ops : List Sse.Op) : List RingSubmission :=
  (Sse.delivered c ops).map submissionOf

/-- **The event stream on the running reactor path.** The submissions the
reactor delivers to subscriber `c` over a session whose subscription was opened
by the reactor's own `dispatch`. -/
def sseServe (cfg : Proto.Config) (c : Sse.SubId) (input : Bytes)
    (ops : List Sse.Op) : List RingSubmission :=
  fanOut c (sseSession cfg c input ops)

/-! ## Composition lemmas -/

/-- A dispatch-headed submission list opens exactly `c`'s subscription. -/
theorem subscribeOnDispatch_dispatch (c : Sse.SubId) (req : Request)
    (rest : List RingSubmission) :
    subscribeOnDispatch c (RingSubmission.dispatch req :: rest)
      = [Sse.Op.subscribe c] := rfl

/-- The response byte-chunks of the fan-out (through the deployed `serve`
path's own send extractor `Reactor.sendsOf`) are exactly the encoded delivered
events, in log order. -/
theorem sendsOf_map_submissionOf (l : List (Nat × Sse.Event)) :
    Reactor.sendsOf (l.map submissionOf) = l.map (fun p => eventBytes p.2) := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    have hstep : Reactor.sendsOf (submissionOf p :: rest.map submissionOf)
        = eventBytes p.2 :: Reactor.sendsOf (rest.map submissionOf) := rfl
    rw [List.map_cons, hstep, ih, List.map_cons]

/-! ## The seam theorems -/

/-- **`sse_fanout_seam` — fan-out soundness on the running path.** What the
reactor delivers to subscriber `c` is exactly the image of the REAL
broadcaster's delivery log (`Sse.delivered`), and that log is an
order-preserving **subsequence** of the global published stream with strictly
increasing sequence tags: every delivered event was published, publish order is
kept, nothing is duplicated. The final conjunct reads the byte-chunks back out
with the deployed path's own `Reactor.sendsOf`: the wire carries the encoded
delivered events, in order. -/
theorem sse_fanout_seam (cfg : Proto.Config) (c : Sse.SubId) (input : Bytes)
    (ops : List Sse.Op) :
    sseServe cfg c input ops
        = (Sse.delivered c (sseSession cfg c input ops)).map submissionOf
      ∧ List.Sublist (Sse.delivered c (sseSession cfg c input ops))
          (Sse.published (sseSession cfg c input ops))
      ∧ (Sse.delivered c (sseSession cfg c input ops)).Pairwise
          (fun a b => a.1 < b.1)
      ∧ Reactor.sendsOf (sseServe cfg c input ops)
        = (Sse.delivered c (sseSession cfg c input ops)).map
            (fun p => eventBytes p.2) :=
  ⟨rfl,
   Sse.delivered_sublist_published c _,
   Sse.delivered_pairwise c _,
   sendsOf_map_submissionOf _⟩

/-- **`sse_no_gap` — fan-out completeness on the running path.** When the
PROVEN reactor dispatches the request (`hsub` — the subscription was opened on
the reactor's own dispatch seam) and the client is never unsubscribed over the
following trace, the reactor delivers **every** published event, in publish
order, with the sequence tags `0, 1, …` intact: the delivery is the published
stream itself (`Sse.delivered_split` composed through the reactor). No gap, no
drop, no reorder. -/
theorem sse_no_gap (cfg : Proto.Config) (c : Sse.SubId) (input : Bytes)
    (ops : List Sse.Op) (req : Request) (rest : List RingSubmission)
    (hsub : ProxyServe.reactorSubs cfg input = RingSubmission.dispatch req :: rest)
    (hnu : Sse.NoUnsub c ops) :
    sseServe cfg c input ops = (Sse.published ops).map submissionOf := by
  have hsession : sseSession cfg c input ops = [Sse.Op.subscribe c] ++ ops := by
    unfold sseSession
    rw [hsub, subscribeOnDispatch_dispatch]
  have hmem : c ∈ Sse.subs [Sse.Op.subscribe c] := Sse.mem_addSub_self [] c
  have hd : Sse.delivered c ([Sse.Op.subscribe c] ++ ops)
      = Sse.publishedAux 0 ops := by
    rw [Sse.delivered_split c [Sse.Op.subscribe c] ops hmem hnu]
    rfl
  unfold sseServe fanOut
  rw [hsession, hd]
  rfl

/-- The wire view of `sse_no_gap`: the byte-chunks the deployed send extractor
sees are exactly the encoded published events, in publish order. -/
theorem sse_no_gap_bytes (cfg : Proto.Config) (c : Sse.SubId) (input : Bytes)
    (ops : List Sse.Op) (req : Request) (rest : List RingSubmission)
    (hsub : ProxyServe.reactorSubs cfg input = RingSubmission.dispatch req :: rest)
    (hnu : Sse.NoUnsub c ops) :
    Reactor.sendsOf (sseServe cfg c input ops)
      = (Sse.published ops).map (fun p => eventBytes p.2) := by
  rw [sse_no_gap cfg c input ops req rest hsub hnu]
  exact sendsOf_map_submissionOf _

/-- **Silence without a subscription.** If the reactor produced no `dispatch`
for the input (the FSM refused the request — `subscribeOnDispatch` found
nothing) and the trace never subscribes `c` either, the reactor delivers
nothing to `c` — no invented events for a connection that never subscribed
(`Sse.deliveredAux_silent` through the reactor). -/
theorem sse_no_dispatch_silent (cfg : Proto.Config) (c : Sse.SubId)
    (input : Bytes) (ops : List Sse.Op)
    (hnone : subscribeOnDispatch c (ProxyServe.reactorSubs cfg input) = [])
    (hnr : Sse.NoResub c ops) :
    sseServe cfg c input ops = [] := by
  unfold sseServe fanOut sseSession
  rw [hnone]
  have hd : Sse.delivered c ([] ++ ops) = [] :=
    Sse.deliveredAux_silent c Sse.BState.init ops
      (by intro h; cases h) hnr
  rw [hd]
  rfl

/-! ## The demo: a concrete broadcast

Two events published after a reactor-dispatched subscribe at `Config.demoConfig`
(the config the test view `serve` runs): the subscriber receives exactly the two
encoded frames, in publish order. `main` runs `Reactor.Deploy.serveFull` over
`deployConfig`; the deployed-path form is `sse_fanout_deployed`. -/

/-- A one-data-line demo event (`data: <b>`). -/
def demoEvent (b : UInt8) : Sse.Event := ⟨none, none, none, [[b]]⟩

/-- The demo broadcast trace: publish `data: 1`, then `data: 2`. -/
def demoOps : List Sse.Op :=
  [Sse.Op.publish (demoEvent 49), Sse.Op.publish (demoEvent 50)]

/-- **The fan-out seam at the demo config (test view).** Any input the test-view
reactor (`Reactor.reactorSubs` = `Reactor.step Config.demoConfig`) turns into a
dispatch opens the subscription, and the two published events are delivered as
exactly their two encoded frames, in order — sequence tags 0 then 1. The
deployed-path form is `sse_fanout_deployed`. -/
theorem demo_sse_fanout (input : Bytes) (req : Request)
    (rest : List RingSubmission)
    (hsub : Reactor.reactorSubs input = RingSubmission.dispatch req :: rest) :
    sseServe Reactor.Config.demoConfig 0 input demoOps
      = [RingSubmission.submitSend (eventBytes (demoEvent 49)),
         RingSubmission.submitSend (eventBytes (demoEvent 50))] := by
  have hsub' : ProxyServe.reactorSubs Reactor.Config.demoConfig input
      = RingSubmission.dispatch req :: rest := hsub
  rw [sse_no_gap Reactor.Config.demoConfig 0 input demoOps req rest hsub'
    (show Sse.NoUnsub 0 demoOps from trivial)]
  rfl

/-! ## The deployed path — fan-out over `Reactor.Deploy.deploySubs`

`Arena.Orb.main` runs `Reactor.Deploy.serveFull` / `deployStep` over
`deployConfig`; the submissions its reactor produces are
`Reactor.Deploy.deploySubs`, and `ProxyServe.reactorSubs Reactor.Deploy.deployConfig`
is `deploySubs` definitionally (`deploy_reactorSubs`). Running the broadcaster
session at that config opens the subscription on the deployed reactor's own
`dispatch`. -/

/-- The SSE session at the deployed config is opened by the deployed reactor's
own submissions: `ProxyServe.reactorSubs deployConfig` is `Reactor.Deploy.deploySubs`. -/
theorem deploy_reactorSubs (input : Bytes) :
    ProxyServe.reactorSubs Reactor.Deploy.deployConfig input
      = Reactor.Deploy.deploySubs input := rfl

/-- **`sse_fanout_deployed` — fan-out completeness on the deployed path.** When
the DEPLOYED reactor (`Reactor.Deploy.deploySubs`, the producer behind `main`'s
`serveFull`) dispatches the request, the subscription opens on that dispatch and
the two published demo events are delivered as exactly their two encoded frames,
in publish order (sequence tags 0 then 1) — `sse_no_gap` at `deployConfig`,
triggered on `Reactor.Deploy.deploySubs`. -/
theorem sse_fanout_deployed (input : Bytes) (req : Request)
    (rest : List RingSubmission)
    (hsub : Reactor.Deploy.deploySubs input = RingSubmission.dispatch req :: rest) :
    sseServe Reactor.Deploy.deployConfig 0 input demoOps
      = [RingSubmission.submitSend (eventBytes (demoEvent 49)),
         RingSubmission.submitSend (eventBytes (demoEvent 50))] := by
  rw [← deploy_reactorSubs] at hsub
  rw [sse_no_gap Reactor.Deploy.deployConfig 0 input demoOps req rest hsub
    (show Sse.NoUnsub 0 demoOps from trivial)]
  rfl

end Reactor.Sse
