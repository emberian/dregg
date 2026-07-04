import Reactor.Contract
import Reactor.Serve
import Reactor.Deploy
import Proto.Theorems

/-!
# Reactor.KeepAlive — the pipelining / keep-alive driver

The demo `serve`'s `demoResp` answers only the *first* request on a connection:
it walks the submission list but returns a single `Response` for the first
`dispatch` it meets, dropping every subsequent pipelined request. Yet the FSM
already does the right thing — `Proto.h1Loop` parses requests from the head of
the accumulation *repeatedly*, emitting one `Output.dispatch req` per request, in
order (`Proto/Step.lean`), and the reactor translates each faithfully
(`ofOutput (.dispatch req) = .dispatch req`). The gap is purely at the reactor's
response half.

This file closes it. `respondEach` is a reactor-level driver that walks the whole
submission list and produces **one response per dispatched request, in order**;
`driveKeepAlive` concatenates them onto the wire. A pipelined pair therefore
yields two responses, not one.

## The seam

`keepalive_all_dispatched` is the composition fact: for any recv event, the
driver's response list is *exactly* the FSM's dispatched requests mapped to
responses, in order. It is proved by composing

* `reactor_carries_dispatches` — the reactor step carries every FSM
  `Output.dispatch` through to a `RingSubmission.dispatch`, in order (the extra
  copy-once `recycleBuffer` submission is not a dispatch and drops out), and
* `respondEach_eq_map` — the driver emits one response per dispatch submission.

`keepalive_discipline` then wires this to the FSM residual-preservation theorem
`Proto.residual_suffix_plainH1`: on a plaintext HTTP/1.1 connection a recv event
both (a) answers every dispatched request in order and (b) leaves the successor
either closed or holding a *suffix* of the accumulation — so the next recv
resumes the pipeline where this one stopped, with no bytes dropped. That is the
full keep-alive discipline: in-order handling of all pipelined requests now,
residual carried for the requests still to come.
-/

namespace Reactor

open Proto (Bytes)

/-! ## Extracting the dispatched requests, in order -/

/-- The dispatched requests carried by a list of FSM outputs, in emission
order. -/
def dispatchOuts : List Proto.Output → List Proto.Request
  | [] => []
  | .dispatch req :: rest => req :: dispatchOuts rest
  | _ :: rest => dispatchOuts rest

/-- The dispatched requests carried by a list of reactor submissions, in order.
(`ofOutput` maps `Output.dispatch` to `RingSubmission.dispatch`, so this mirrors
`dispatchOuts` across the translation.) -/
def dispatchSubs : List RingSubmission → List Proto.Request
  | [] => []
  | .dispatch req :: rest => req :: dispatchSubs rest
  | _ :: rest => dispatchSubs rest

/-- `dispatchSubs` distributes over concatenation. -/
theorem dispatchSubs_append (a b : List RingSubmission) :
    dispatchSubs (a ++ b) = dispatchSubs a ++ dispatchSubs b := by
  induction a with
  | nil => rfl
  | cons x t ih => cases x <;> simp [dispatchSubs, ih]

/-- Translating the FSM outputs preserves the dispatched-request sequence: the
requests recovered from the translated submissions are exactly those the FSM
dispatched, in order. -/
theorem dispatchSubs_map_ofOutput (outs : List Proto.Output) :
    dispatchSubs (outs.map ofOutput) = dispatchOuts outs := by
  induction outs with
  | nil => rfl
  | cons o t ih => cases o <;> simp [dispatchSubs, dispatchOuts, ofOutput, ih]

/-- **The reactor carries every FSM dispatch through, in order.** A recv event's
submission list recovers exactly the FSM's dispatched requests: the per-output
translation is faithful and the appended copy-once `recycleBuffer` is not a
dispatch. This is the composition point between the FSM's pipelining loop and the
reactor's response driver. -/
theorem reactor_carries_dispatches (cfg : Proto.Config) (s : Proto.State)
    (bid : Uring.Bid) (data : Bytes) :
    dispatchSubs (Reactor.step cfg s (.recvInto bid data)).2
      = dispatchOuts (Proto.step cfg s (.bytesReceived data)).2 := by
  have h : (Reactor.step cfg s (.recvInto bid data)).2
      = (Proto.step cfg s (.bytesReceived data)).2.map ofOutput
          ++ [RingSubmission.recycleBuffer bid] := rfl
  rw [h, dispatchSubs_append,
     show dispatchSubs [RingSubmission.recycleBuffer bid] = [] from rfl,
     List.append_nil, dispatchSubs_map_ofOutput]

/-! ## The driver: one response per dispatched request -/

/-- The application response bytes for one dispatched request — the proven
serializer's `200 OK` reflecting the resolved head (reusing `Serve.okBody`).
Every response byte is `serialize` of a `Response`, so each carries
`serialize_framing`. -/
def appResponse (req : Proto.Request) : Bytes := serialize (ok200 (okBody req))

/-- **The keep-alive responder.** Walk the whole submission list and emit one
response for *every* `dispatch`, in order (unlike `demoResp`, which stops at the
first). Non-dispatch submissions are skipped here (the FSM's own sends are
forwarded by `Serve.serve`; this driver is the application-response half). -/
def respondEach : List RingSubmission → List Bytes
  | [] => []
  | .dispatch req :: rest => appResponse req :: respondEach rest
  | _ :: rest => respondEach rest

/-- Concatenate the per-request responses onto the wire, in order. -/
def driveKeepAlive (subs : List RingSubmission) : Bytes := (respondEach subs).flatten

/-- The driver emits exactly one response per dispatched request, in order. -/
theorem respondEach_eq_map (subs : List RingSubmission) :
    respondEach subs = (dispatchSubs subs).map appResponse := by
  induction subs with
  | nil => rfl
  | cons x t ih => cases x <;> simp [respondEach, dispatchSubs, ih]

/-! ## The seam theorem -/

/-- **`keepalive_all_dispatched` — every dispatched request gets a response, in
order.** For any recv event, the reactor driver's response list is exactly the
FSM's dispatched requests mapped to responses, in the same order. A pipelined
pair (two `Output.dispatch` in the FSM output) yields two responses, not one.
Composes `reactor_carries_dispatches` (FSM→reactor dispatch fidelity) with
`respondEach_eq_map` (one response per dispatch). -/
theorem keepalive_all_dispatched (cfg : Proto.Config) (s : Proto.State)
    (bid : Uring.Bid) (data : Bytes) :
    respondEach (Reactor.step cfg s (.recvInto bid data)).2
      = (dispatchOuts (Proto.step cfg s (.bytesReceived data)).2).map appResponse := by
  rw [respondEach_eq_map, reactor_carries_dispatches]

/-- **Response count matches dispatch count.** The number of responses the driver
emits equals the number of requests the FSM dispatched — so no request is
silently dropped and none is answered twice. -/
theorem keepalive_response_count (cfg : Proto.Config) (s : Proto.State)
    (bid : Uring.Bid) (data : Bytes) :
    (respondEach (Reactor.step cfg s (.recvInto bid data)).2).length
      = (dispatchOuts (Proto.step cfg s (.bytesReceived data)).2).length := by
  rw [keepalive_all_dispatched, List.length_map]

/-- **Pipelined-pair witness.** Two dispatched requests in one submission list
yield two responses, in order — where a first-only responder would produce
one. -/
theorem respondEach_pipelined_pair (r₁ r₂ : Proto.Request) (bid : Uring.Bid) :
    respondEach [.dispatch r₁, .dispatch r₂, .recycleBuffer bid]
      = [appResponse r₁, appResponse r₂] := rfl

/-- **`keepalive_discipline` — the full keep-alive seam.** On a plaintext
HTTP/1.1 connection, a recv event both

* (a) answers **every** dispatched request in order — the reactor driver's
  responses are exactly the FSM's dispatches mapped to responses, and
* (b) leaves the successor either **closed** or holding a **suffix** of the whole
  accumulation `(buf ++ data).drop k` — no unconsumed byte is dropped, so the
  next recv resumes the pipeline exactly where this one stopped.

Part (b) is the FSM's `residual_suffix_plainH1` lifted to the reactor state
(`Reactor.step` returns the FSM successor unchanged). Together (a)+(b) are the
keep-alive discipline: all pipelined requests handled now, the residual carried
for the ones still arriving. -/
theorem keepalive_discipline (cfg : Proto.Config) (c : Proto.Conn)
    (buf data : Bytes) (bid : Uring.Bid) (hp : c.proto = .plainH1 buf) :
    respondEach (Reactor.step cfg (.active c) (.recvInto bid data)).2
        = (dispatchOuts (Proto.step cfg (.active c) (.bytesReceived data)).2).map appResponse
    ∧ ((Reactor.step cfg (.active c) (.recvInto bid data)).1 = .closed
        ∨ ∃ c' k, (Reactor.step cfg (.active c) (.recvInto bid data)).1 = .active c'
            ∧ c'.proto = .plainH1 ((buf ++ data).drop k)) := by
  refine ⟨keepalive_all_dispatched cfg (.active c) bid data, ?_⟩
  have hstate : (Reactor.step cfg (.active c) (.recvInto bid data)).1
      = (Proto.step cfg (.active c) (.bytesReceived data)).1 := rfl
  rw [hstate]
  exact Proto.residual_suffix_plainH1 cfg c buf data hp

/-! ## The deployed path

The keep-alive seams above are generic over the `Proto.Config`. The deployed orb
runs the reactor over `Reactor.Deploy.deployConfig` on the submission list
`Reactor.Deploy.deploySubs input` (definitionally `(Reactor.step deployConfig
(active mkPlain) (recvInto 0 input)).2`). Instantiating the generic seams at
`deployConfig` / the fresh plain connection lands them on exactly that list —
the requests the deployed binary answers. -/

/-- **`keepalive_all_dispatched_deployed` — every dispatched request on the
DEPLOYED submission list gets a response, in order.** The deployed reactor's
per-request response driver emits exactly the FSM's dispatched requests mapped to
responses, in emission order, over `deployConfig`. This is
`keepalive_all_dispatched` instantiated at the deployed config and the fresh plain
connection, so it is a fact about `Reactor.Deploy.deploySubs input` — the very
list `main` acts on. -/
theorem keepalive_all_dispatched_deployed (input : Bytes) :
    respondEach (Reactor.Deploy.deploySubs input)
      = (dispatchOuts (Proto.step Reactor.Deploy.deployConfig
          (.active Proto.Conn.mkPlain) (.bytesReceived input)).2).map appResponse :=
  keepalive_all_dispatched Reactor.Deploy.deployConfig
    (.active Proto.Conn.mkPlain) 0 input

/-- **`keepalive_discipline_deployed` — the full keep-alive discipline on the
DEPLOYED path.** From the fresh plain connection the deployed orb starts on
(`Conn.mkPlain`, whose protocol state is `.plainH1 []`), a recv both (a) answers
every dispatched request in order and (b) leaves the successor either closed or
holding a suffix of the accumulation — so the next recv resumes the deployed
pipeline where this one stopped. `keepalive_discipline` instantiated at
`deployConfig` / `mkPlain`. -/
theorem keepalive_discipline_deployed (input : Bytes) :
    respondEach (Reactor.Deploy.deploySubs input)
        = (dispatchOuts (Proto.step Reactor.Deploy.deployConfig
            (.active Proto.Conn.mkPlain) (.bytesReceived input)).2).map appResponse
    ∧ ((Reactor.step Reactor.Deploy.deployConfig
          (.active Proto.Conn.mkPlain) (.recvInto 0 input)).1 = .closed
        ∨ ∃ c' k, (Reactor.step Reactor.Deploy.deployConfig
              (.active Proto.Conn.mkPlain) (.recvInto 0 input)).1 = .active c'
            ∧ c'.proto = .plainH1 (([] ++ input).drop k)) :=
  keepalive_discipline Reactor.Deploy.deployConfig Proto.Conn.mkPlain [] input 0 rfl

end Reactor
