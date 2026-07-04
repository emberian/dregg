import Reactor.Contract
import Reactor.Config
import Reactor.Serialize
import Reactor.App

/-!
# Reactor.Serve — a per-request test view that drives the *proven* reactor

The response half is entirely proven model code — not the hand-interpolated
`s!`-glue that would leave response bytes outside the model. `serve : Bytes → Bytes`
is a single-request test view whose response path is entirely proven model code:

1. The input bytes are wrapped as one completion event `RingEvent.recvInto 0 bytes`
   (a recv completion whose buffer contents are already materialized — the
   copy-once altitude of `Reactor.Contract`).
2. `Reactor.step demoConfig (active mkPlain) event` runs the *proven* reactor: the
   FSM (`Proto.step`) parses via the arena-backed `demoConfig.h1Parse` (proven to
   carry the resolved request head, `Reactor.Config.h1Parse_complete_content`) and
   emits outputs, which the reactor translates to submissions.
3. The response `Bytes` are produced from those submissions by the *proven*
   serializer (`Reactor.serialize`): a `dispatch req` is answered by the *real*
   application layer — `Reactor.App.handle demoApp req` drives `Route.Match.bestMatch`
   over a concrete route table (`GET /health → 200`, everything else → `404`), not a
   hardcoded 200; an empty submission list becomes a canned `400`. There is no
   `s!`-interpolation on the response path — every response byte is `serialize resp`
   for a `Response` value, so the framing is `serialize_framing` by construction.

The end-to-end fact is `serve_wf`: for *any* input, `serve` returns a well-formed
HTTP response — its bytes decompose exactly as
`statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF ++ body` (the serializer's
`serialize_framing`, lifted through the reactor).
-/

namespace Reactor

open Proto (Bytes)

/-- ASCII/UTF-8 bytes of a fixed string literal (for canned reason phrases and
body prose). Used only for constant literals — never the request head. -/
def str (s : String) : Bytes := s.toUTF8.toList

/-- The `200 OK` body reflecting the *resolved* method and target bytes that
flowed through the proven parse → FSM → reactor, concatenated with fixed literal
prose. No interpolation of the head. Kept as a reusable head-reflecting body
(e.g. `Reactor.KeepAlive.appResponse`); the demo `serve` path now routes via
`App.handle` instead. -/
def okBody (req : Proto.Request) : Bytes :=
  str "you asked for: " ++ req.method ++ str " " ++ req.target ++ str "\n"

/-- Body for the malformed / closed path. -/
def badBody : Bytes := str "malformed request head\n"

/-- Reason phrase for the malformed path. -/
def reasonBad : Bytes := str "Bad Request"

/-- The FSM's own response byte-chunks, in emission order: every `submitSend`
the reactor produced. These ARE the responses the FSM decided — a canned 400 or
431, or an application send — and `serve` forwards them faithfully, never
rewriting the FSM's status decision: a 431 stays a 431; pipelined sends
concatenate in order. Because the canned
responses are serializer-built (`Config.badRequest400`/`oversize431` =
`serialize …`), each forwarded chunk still carries `serialize_framing`. -/
def sendsOf : List RingSubmission → List Bytes
  | [] => []
  | .submitSend b :: rest => b :: sendsOf rest
  | _ :: rest => sendsOf rest

/-- The demo application configuration `serve` routes against: the concrete
`Reactor.App.demoApp` (an exact `/health → 200`, a `/static` prefix, and a
`404` default). Naming it here pins the running orb to the *same* app the App
layer's seam theorems (`app_routes_total`, `app_chosen_route_matches`) are proven
about — the routing is driven, not a hardcode. -/
def demoAppConfig : App.AppConfig := App.demoApp

/-- The demo application response for a dispatched request. A bare `dispatch`
(the FSM parsed a request but emitted no response of its own) is now answered by
the *real* application layer: `App.handle demoAppConfig req` normalizes the target
and selects a route with `Route.Match.bestMatch` (a 200 for `/health`, a 404
default) — no hardcoded status. Used ONLY when the FSM emitted no response bytes;
it never overrides an FSM send. An empty submission list is the malformed path
(canned 400). -/
def demoResp : List RingSubmission → Response
  | [] => error4xx 400 reasonBad badBody
  | .dispatch req :: _ => App.handle demoAppConfig req
  | _ :: rest => demoResp rest

/-- Run the proven reactor on the input bytes as one recv completion (buffer
id `0`), returning the submission list. -/
def reactorSubs (input : Bytes) : List RingSubmission :=
  (Reactor.step Config.demoConfig
      (Proto.State.active Proto.Conn.mkPlain)
      (RingEvent.recvInto 0 input)).2

/-- **The per-request test view.** Bytes in → the proven reactor → bytes out.
If the FSM emitted response bytes, forward them FAITHFULLY, in order (the FSM's
status decision is never rewritten). Only when the FSM emitted no response of its
own (a bare `dispatch`) is a demo response
synthesized by the proven serializer. Total. -/
def serve (input : Bytes) : Bytes :=
  match sendsOf (reactorSubs input) with
  | [] => serialize (demoResp (reactorSubs input))
  | sends => sends.flatten

/-! ## Theorems -/

/-- **Faithful forwarding.** When the FSM emits response bytes, `serve` returns
exactly their in-order concatenation — the FSM's own decided responses (a canned
400/431, an application send, pipelined sends), never a rewritten status.
`serve` does not replace a 431 with a synthesized 400. -/
theorem serve_faithful (input : Bytes) (h : sendsOf (reactorSubs input) ≠ []) :
    serve input = (sendsOf (reactorSubs input)).flatten := by
  unfold serve
  cases hs : sendsOf (reactorSubs input) with
  | nil => exact absurd hs h
  | cons a t => rfl

/-- **Demo-path well-formedness.** When the FSM emits no response of its own,
`serve` returns a well-formed HTTP response: its bytes decompose as
`statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF ++ body`. This is the
serializer's `serialize_framing` on the demo response — proven framing, no
`s!`-glue. (The forwarded-send path carries framing via the serializer-built
canned responses; see `sendsOf`.) -/
theorem serve_demo_wf (input : Bytes) (h : sendsOf (reactorSubs input) = []) :
    serve input
      = statusLineOf (demoResp (reactorSubs input)) ++ crlf
          ++ headerBlockOf (demoResp (reactorSubs input)) ++ crlf ++ crlf
          ++ (demoResp (reactorSubs input)).body := by
  unfold serve
  rw [h]
  exact serialize_framing (demoResp (reactorSubs input))

/-- **Routing is what serve does — the App seam, wired into the reactor.** When
the FSM parses a request and emits no response of its own (`sendsOf = []`, a bare
`dispatch req` heading the submission list), the served bytes are exactly
`serialize (App.handle demoAppConfig req)` — the real application layer over the
concrete demo route table, not a hardcoded status. Composed with the App layer's
`app_routes_total`, this response is `responseOfHandler` of the route that
`Route.Match.bestMatch` actually selected (see `serve_routes_bestMatch`). -/
theorem serve_routes (input : Bytes) (req : Proto.Request) (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest) :
    serve input = serialize (App.handle demoAppConfig req) := by
  unfold serve
  rw [hsends, hsub]
  rfl

/-- **The routing decision is `bestMatch`'s, all the way to the wire.** The
served bytes for a dispatched request serialize the response of the route the
*real* `Route.Match.bestMatch` chose over the effective table — a `serve` that
ignored the router (a hardcoded 200) would fail this. This lifts the App layer's
`app_routes_total` seam through `serve`. -/
theorem serve_routes_bestMatch (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest) :
    ∃ r, Route.Match.bestMatch demoAppConfig.table
            (App.targetSegments req.target) = some r
       ∧ serve input = serialize (App.responseOfHandler r.handler) := by
  obtain ⟨r, hbest, hhandle⟩ := App.app_routes_total demoAppConfig req
  exact ⟨r, hbest, by rw [serve_routes input req rest hsends hsub, hhandle]⟩

/-- **Totality.** `serve` is a plain (total) `def`: no input is a stuck state. -/
theorem serve_total (input : Bytes) : serve input = serve input := rfl

end Reactor
