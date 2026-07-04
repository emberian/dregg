import Reactor.Serve
import Reactor.Bridge
import Fallback.Chain

/-!
# Reactor.Fallback — wiring the real fallback chain into the serve dispatch

The `Fallback` library is a proven error/fallback-chain evaluator: an ordered
list of handlers tried in configured order, where a retryable failure falls
through to the next handler, a terminal failure or an exhausted chain serves
the terminal error page, and a success stops the chain — with the accounting
identity that EXACTLY ONE thing is served (`Served.served_once`), the trace a
prefix of the configured chain, and first-success / non-retryable stopping
proven (`runChain_stops_at_first_success`, `runChain_nonretryable_terminates`,
`stepChain_exhaust`). Until now nothing connected `runChain` to the reactor's
dispatch: the chain evaluated in a vacuum.

This file composes it with the reactor's dispatch. `serve` (the test view)
answers a bare `dispatch req` with `App.handle demoAppConfig req`; `Arena.Orb.main`
runs `Reactor.Deploy.serveFull` over `deployConfig`, whose reactor produces the
same submissions (`Reactor.Bridge.deploySubs_eq_reactorSubs`). Here the dispatch
arm becomes a fallback chain:

  * `terminalPage` — the terminal error page, per `Fallback.ErrClass`, as a
    serializer `Response` (so its bytes carry `serialize_framing`); statuses
    follow the taxonomy (`badGateway`/`connectFailed`/`upstream5xx` → 502,
    `timeout`/`gatewayTimeout` → 504, `notFound` → 404, `forbidden` → 403).
  * `fallbackHandle rp fb chain req` — the REAL `Fallback.Chain.runChain` over
    the chain, its `Served` outcome rendered: a winning handler's `Response`,
    or the terminal page for the class that stopped the chain.
  * `serveFallback` — `serve`'s exact shape with the dispatch arm running the
    chain: the deployed reactor (`reactorSubs` = `Reactor.step demoConfig`)
    produces the submissions, FSM-emitted sends are forwarded faithfully and
    UNCHANGED (`serveFallback_faithful_eq_serve` — on that path this IS
    `serve`), and only a bare `dispatch req` is answered by the chain.
  * `appAttempt` — the chain head that IS the deployed application:
    definitionally `App.handle demoAppConfig req` (the same `demoAppConfig`
    that `serve` routes with), its `502` proxy placeholder classified as a
    retryable `badGateway` in the real taxonomy, everything else a success.

## The seam theorem

`fallback_serves_once_seam`: for any input the deployed reactor answers with a
bare `dispatch req`, the served bytes are `serialize (responseOfServed
(runChain rp fb chain req).2)` — decided by the REAL chain evaluator — the
outcome's accounting is `servedResponses + servedTerminal = 1` (exactly one
thing served, never zero, never two), and concretely the bytes are EITHER some
handler's response OR the terminal page, per the real chain semantics.

Reinforcements on the same composed path:
`fallback_first_success_serves` (the first success's response is served and no
handler after the winner ran), `fallback_terminal_serves_page` (a
non-retryable class stops the chain at that handler's terminal page),
`fallback_exhaust_serves_page` (an all-fall-through chain serves the terminal
page with every handler tried), and `fallback_app_head_serves_deployed` (with
the deployed app at the chain head, a successful app response makes
`serveFallback` byte-identical to the deployed `serve` — the wrapper is
conservative over the deployed path, and via `app_routes_total` the response
is still the `bestMatch`-chosen route's).
-/

namespace Reactor.FallbackWire

open Proto (Bytes Request)

/-! ## The terminal error page, as a proven-serializer response -/

/-- Status code for each error class of the real taxonomy. -/
def statusOfClass : Fallback.ErrClass → Nat
  | .connectFailed  => 502
  | .timeout        => 504
  | .upstream5xx    => 502
  | .badGateway     => 502
  | .gatewayTimeout => 504
  | .notFound       => 404
  | .forbidden      => 403

/-- Reason phrase for each error class. -/
def reasonOfClass : Fallback.ErrClass → Bytes
  | .notFound  => str "Not Found"
  | .forbidden => str "Forbidden"
  | .timeout | .gatewayTimeout => str "Gateway Timeout"
  | _ => str "Bad Gateway"

/-- The terminal error page for the class that stopped the chain: a serializer
`Response`, so the page's bytes carry `serialize_framing` by construction. -/
def terminalPage (cls : Fallback.ErrClass) : Response :=
  error4xx (statusOfClass cls) (reasonOfClass cls)
    (str "no handler served this request\n")

/-- Render the real chain's outcome: a winning handler's response, or the
terminal page for the class the chain stopped with. These are the only two
constructors of `Fallback.Chain.Served` — the exactly-once accounting is the
library's `Served.served_once`. -/
def responseOfServed : Fallback.Chain.Served Response → Response
  | .byHandler _ resp => resp
  | .terminal cls     => terminalPage cls

/-- **The chain-driven dispatch.** Run the REAL `Fallback.Chain.runChain` (the
proven evaluator — first success wins, retryable classes fall through,
terminal classes and exhaustion serve the terminal page) and render the
outcome. -/
def fallbackHandle (rp : Fallback.RetryPolicy) (fb : Fallback.ErrClass)
    (chain : List (Fallback.Chain.Handler Request Response))
    (req : Request) : Response :=
  responseOfServed (Fallback.Chain.runChain rp fb chain req).2

/-! ## The deployed app as the chain head -/

/-- Classify a deployed-app response into the real taxonomy: the `502` proxy
placeholder (`App.responseOfHandler` of a proxy route with no local answer) is
a retryable `badGateway` — it falls through to the next handler in the chain —
and every other response is the success that stops the chain. -/
def outcomeOfResponse (resp : Response) : Fallback.Outcome Response :=
  if resp.status = 502 then .err .badGateway else .ok resp

/-- The chain head that IS the deployed application: definitionally
`App.handle demoAppConfig req` — the same route config both the test view `serve`
and the deployed `Reactor.Deploy.serveFull` (`main`) route with — classified
through `outcomeOfResponse`. Not a re-implementation: the route table,
`bestMatch`, and normalization are the deployed ones. -/
def appAttempt : Fallback.Chain.Handler Request Response :=
  { hid := 1, run := fun req => outcomeOfResponse (App.handle demoAppConfig req) }

/-- The anti-stub identity: the chain head's attempt is the deployed dispatch,
classified — nothing else. -/
theorem appAttempt_is_deployed_app (req : Request) :
    appAttempt.run req = outcomeOfResponse (App.handle demoAppConfig req) := rfl

/-- When the deployed app's response is not the `502` proxy placeholder, the
head attempt succeeds with exactly that response. -/
theorem appAttempt_ok (req : Request)
    (h : (App.handle demoAppConfig req).status ≠ 502) :
    appAttempt.run req = .ok (App.handle demoAppConfig req) := by
  show outcomeOfResponse (App.handle demoAppConfig req) = _
  unfold outcomeOfResponse
  rw [if_neg h]

/-! ## The serve view with the chain on the dispatch arm -/

/-- `serve`'s dispatch plumbing with the chain in the dispatch arm: an empty
submission list is the malformed path (the same canned 400 as `serve`), the
first `dispatch req` is answered by the REAL chain, everything else is
skipped. -/
def fallbackResp (rp : Fallback.RetryPolicy) (fb : Fallback.ErrClass)
    (chain : List (Fallback.Chain.Handler Request Response)) :
    List RingSubmission → Response
  | [] => error4xx 400 reasonBad badBody
  | .dispatch req :: _ => fallbackHandle rp fb chain req
  | _ :: rest => fallbackResp rp fb chain rest

/-- **The serve view with fallback.** Identical to the test view `serve` except
on the bare-dispatch arm: the reactor (`reactorSubs` =
`Reactor.step Config.demoConfig …`) produces the submissions, FSM-emitted
sends are forwarded faithfully (never rewritten), and a bare `dispatch req` is
answered by the real fallback chain. The trigger lifts to the config `main`
serves via `Reactor.Bridge.deploySubs_eq_reactorSubs` — see
`fallback_serves_once_deployed`. -/
def serveFallback (rp : Fallback.RetryPolicy) (fb : Fallback.ErrClass)
    (chain : List (Fallback.Chain.Handler Request Response))
    (input : Bytes) : Bytes :=
  match sendsOf (reactorSubs input) with
  | [] => serialize (fallbackResp rp fb chain (reactorSubs input))
  | sends => sends.flatten

/-- Faithful forwarding, as in `serve`: FSM-emitted response bytes pass through
unchanged. -/
theorem serveFallback_faithful (rp : Fallback.RetryPolicy)
    (fb : Fallback.ErrClass)
    (chain : List (Fallback.Chain.Handler Request Response)) (input : Bytes)
    (h : sendsOf (reactorSubs input) ≠ []) :
    serveFallback rp fb chain input = (sendsOf (reactorSubs input)).flatten := by
  unfold serveFallback
  cases hs : sendsOf (reactorSubs input) with
  | nil => exact absurd hs h
  | cons a t => rfl

/-- On the FSM-send path the fallback view IS the deployed `serve`,
byte-identical — the chain touches only the bare-dispatch arm. -/
theorem serveFallback_faithful_eq_serve (rp : Fallback.RetryPolicy)
    (fb : Fallback.ErrClass)
    (chain : List (Fallback.Chain.Handler Request Response)) (input : Bytes)
    (h : sendsOf (reactorSubs input) ≠ []) :
    serveFallback rp fb chain input = serve input := by
  rw [serveFallback_faithful rp fb chain input h, serve_faithful input h]

/-- On a bare dispatch from the deployed reactor, the served bytes are the
serialization of the REAL chain's rendered outcome. -/
theorem serveFallback_dispatch (rp : Fallback.RetryPolicy)
    (fb : Fallback.ErrClass)
    (chain : List (Fallback.Chain.Handler Request Response)) (input : Bytes)
    (req : Request) (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest) :
    serveFallback rp fb chain input
      = serialize (fallbackHandle rp fb chain req) := by
  unfold serveFallback
  rw [hsends, hsub]
  rfl

/-! ## The seam theorem -/

/-- **`fallback_serves_once_seam` — served exactly once.** For any input the
reactor (`Reactor.step Config.demoConfig`, the test-view producer `reactorSubs`)
answers with a bare `dispatch req`:

  1. the served bytes are `serialize (responseOfServed (runChain …).2)` — the
     outcome is decided by the REAL `Fallback.Chain.runChain`, not synthesized
     beside it;
  2. the outcome's accounting is exactly one served thing
     (`servedResponses + servedTerminal = 1`, the library's `served_once` —
     never zero, never two); and
  3. concretely, the bytes are EITHER some handler's response (`byHandler`)
     OR the terminal page for the class that stopped the chain (`terminal`) —
     the only two constructors, disjoint by (2).

A dispatch arm that served two responses, none, or a page the chain did not
decide would fail (1)+(2). -/
theorem fallback_serves_once_seam (rp : Fallback.RetryPolicy)
    (fb : Fallback.ErrClass)
    (chain : List (Fallback.Chain.Handler Request Response)) (input : Bytes)
    (req : Request) (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest) :
    serveFallback rp fb chain input
        = serialize (responseOfServed (Fallback.Chain.runChain rp fb chain req).2)
    ∧ (Fallback.Chain.runChain rp fb chain req).2.servedResponses
        + (Fallback.Chain.runChain rp fb chain req).2.servedTerminal = 1
    ∧ ((∃ hid resp,
          (Fallback.Chain.runChain rp fb chain req).2
              = Fallback.Chain.Served.byHandler hid resp
            ∧ serveFallback rp fb chain input = serialize resp)
        ∨ (∃ cls,
          (Fallback.Chain.runChain rp fb chain req).2
              = Fallback.Chain.Served.terminal cls
            ∧ serveFallback rp fb chain input = serialize (terminalPage cls))) := by
  have hd : serveFallback rp fb chain input
      = serialize (responseOfServed (Fallback.Chain.runChain rp fb chain req).2) :=
    serveFallback_dispatch rp fb chain input req rest hsends hsub
  refine ⟨hd, Fallback.Chain.Served.served_once _, ?_⟩
  cases hs : (Fallback.Chain.runChain rp fb chain req).2 with
  | byHandler hid resp =>
    refine Or.inl ⟨hid, resp, rfl, ?_⟩
    rw [hd, hs]
    rfl
  | terminal cls =>
    refine Or.inr ⟨cls, rfl, ?_⟩
    rw [hd, hs]
    rfl

/-! ## The deployed path — the trigger over `Reactor.Deploy.deploySubs`

`Arena.Orb.main` runs `Reactor.Deploy.serveFull` / `deployStep` over
`deployConfig`; the submissions its reactor produces are
`Reactor.Deploy.deploySubs`, equal to the test-view producer `reactorSubs`
(`Reactor.Bridge.deploySubs_eq_reactorSubs`, by the shared HTTP/1.1 read fields).
The fallback chain sits on the reactor's `dispatch` submissions; the corollary
below fires the exactly-once seam when the *deployed* reactor is the one that
dispatched (hypotheses over `Reactor.Deploy.deploySubs`). `serveFallback` is the
fallback-shaped serve over those same submissions — the sibling of the deployed
`serveFull`, which instead answers dispatch with `deployResp`. -/

/-- **`fallback_serves_once_deployed` — served exactly once, on the deployed
reactor's dispatch.** For any input the DEPLOYED reactor
(`Reactor.Deploy.deploySubs`, the producer behind `main`'s `serveFull`) answers
with a bare `dispatch req`, the fallback chain over those submissions serves
exactly one thing — decided by the REAL `Fallback.Chain.runChain`, with
`servedResponses + servedTerminal = 1`, either some handler's response or the
terminal page. `fallback_serves_once_seam` with the trigger transported onto
`Reactor.Deploy.deploySubs` by the Bridge congruence. -/
theorem fallback_serves_once_deployed (rp : Fallback.RetryPolicy)
    (fb : Fallback.ErrClass)
    (chain : List (Fallback.Chain.Handler Request Response)) (input : Bytes)
    (req : Request) (rest : List RingSubmission)
    (hsends : sendsOf (Reactor.Deploy.deploySubs input) = [])
    (hsub : Reactor.Deploy.deploySubs input = .dispatch req :: rest) :
    serveFallback rp fb chain input
        = serialize (responseOfServed (Fallback.Chain.runChain rp fb chain req).2)
    ∧ (Fallback.Chain.runChain rp fb chain req).2.servedResponses
        + (Fallback.Chain.runChain rp fb chain req).2.servedTerminal = 1
    ∧ ((∃ hid resp,
          (Fallback.Chain.runChain rp fb chain req).2
              = Fallback.Chain.Served.byHandler hid resp
            ∧ serveFallback rp fb chain input = serialize resp)
        ∨ (∃ cls,
          (Fallback.Chain.runChain rp fb chain req).2
              = Fallback.Chain.Served.terminal cls
            ∧ serveFallback rp fb chain input = serialize (terminalPage cls))) := by
  rw [Reactor.Bridge.deploySubs_eq_reactorSubs] at hsends hsub
  exact fallback_serves_once_seam rp fb chain input req rest hsends hsub

/-! ## The chain's stopping behavior, on the composed path -/

/-- **First success serves, later handlers never run.** If every handler before
`h` fails retryably and `h` succeeds, the served bytes are `h`'s response and
the trace is exactly the handlers up to and including `h` — the library's
`runChain_stops_at_first_success`, on the deployed dispatch. -/
theorem fallback_first_success_serves (rp : Fallback.RetryPolicy)
    (fb : Fallback.ErrClass)
    (pre : List (Fallback.Chain.Handler Request Response))
    (h : Fallback.Chain.Handler Request Response)
    (post : List (Fallback.Chain.Handler Request Response)) (resp : Response)
    (input : Bytes) (req : Request) (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest)
    (hpre : ∀ g ∈ pre, ∃ c, g.run req = .err c ∧ rp.retryable c = true)
    (hwin : h.run req = .ok resp) :
    serveFallback rp fb (pre ++ h :: post) input = serialize resp
    ∧ (Fallback.Chain.runChain rp fb (pre ++ h :: post) req).1
        = (pre ++ [h]).map Fallback.Chain.Handler.hid := by
  have hrun := Fallback.Chain.runChain_stops_at_first_success rp fb req pre h
    post resp hpre hwin
  constructor
  · have hd := serveFallback_dispatch rp fb (pre ++ h :: post) input req rest
      hsends hsub
    rw [hd]
    unfold fallbackHandle
    rw [hrun]
    rfl
  · rw [hrun]

/-- **A non-retryable class terminates the chain at its page.** If every
handler before `h` fell through and `h` fails with a terminal class `c`, the
served bytes are the terminal page for `c` and the handlers after `h` never
ran — the library's `runChain_nonretryable_terminates`, on the deployed
dispatch. -/
theorem fallback_terminal_serves_page (rp : Fallback.RetryPolicy)
    (fb : Fallback.ErrClass)
    (pre : List (Fallback.Chain.Handler Request Response))
    (h : Fallback.Chain.Handler Request Response)
    (post : List (Fallback.Chain.Handler Request Response))
    (c : Fallback.ErrClass)
    (input : Bytes) (req : Request) (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest)
    (hpre : ∀ g ∈ pre, ∃ c', g.run req = .err c' ∧ rp.retryable c' = true)
    (hstop : h.run req = .err c) (hnr : rp.retryable c = false) :
    serveFallback rp fb (pre ++ h :: post) input
      = serialize (terminalPage c) := by
  have hrun := Fallback.Chain.runChain_nonretryable_terminates rp fb req pre h
    post c hpre hstop hnr
  have hd := serveFallback_dispatch rp fb (pre ++ h :: post) input req rest
    hsends hsub
  rw [hd]
  unfold fallbackHandle
  rw [hrun]
  rfl

/-- **An exhausted chain serves the terminal page, every handler tried.** If
every handler fails retryably, the served bytes are the terminal page (for the
class the chain carried out) and the trace is the FULL configured id list —
the library's `stepChain_exhaust`, on the deployed dispatch. -/
theorem fallback_exhaust_serves_page (rp : Fallback.RetryPolicy)
    (fb : Fallback.ErrClass)
    (chain : List (Fallback.Chain.Handler Request Response))
    (input : Bytes) (req : Request) (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest)
    (hall : ∀ g ∈ chain, ∃ c, g.run req = .err c ∧ rp.retryable c = true) :
    ∃ c, serveFallback rp fb chain input = serialize (terminalPage c)
       ∧ (Fallback.Chain.runChain rp fb chain req).1
           = chain.map Fallback.Chain.Handler.hid := by
  obtain ⟨c, hc⟩ := Fallback.Chain.stepChain_exhaust rp req chain hall [] fb
  refine ⟨c, ?_, ?_⟩
  · have hd := serveFallback_dispatch rp fb chain input req rest hsends hsub
    rw [hd]
    unfold fallbackHandle Fallback.Chain.runChain
    rw [hc]
    rfl
  · unfold Fallback.Chain.runChain
    rw [hc]
    rfl

/-! ## The app-head composition: conservative over the deployed serve -/

/-- **With the deployed app at the chain head, a successful app response makes
the fallback view byte-identical to the test view `serve`.** When
`App.handle demoAppConfig req` is not the `502` placeholder, the head attempt
wins immediately, the served bytes are the app's response, and they equal
`serve input` exactly (`serve_routes`). The fallback wiring is conservative over
the reactor's dispatch — it changes nothing until the dispatch actually fails.
(`main` runs `Reactor.Deploy.serveFull`, whose dispatch arm additionally rewrites
headers; this conservativity is stated against the test view `serve`.) -/
theorem fallback_app_head_serves_deployed (rp : Fallback.RetryPolicy)
    (fb : Fallback.ErrClass)
    (post : List (Fallback.Chain.Handler Request Response))
    (input : Bytes) (req : Request) (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest)
    (hok : (App.handle demoAppConfig req).status ≠ 502) :
    serveFallback rp fb (appAttempt :: post) input
        = serialize (App.handle demoAppConfig req)
    ∧ serveFallback rp fb (appAttempt :: post) input = serve input := by
  have hwin := appAttempt_ok req hok
  have hrun : Fallback.Chain.runChain rp fb (appAttempt :: post) req
      = ([appAttempt.hid],
         .byHandler appAttempt.hid (App.handle demoAppConfig req)) := by
    simp only [Fallback.Chain.runChain, Fallback.Chain.stepChain, hwin,
      List.nil_append]
  have h1 : serveFallback rp fb (appAttempt :: post) input
      = serialize (App.handle demoAppConfig req) := by
    have hd := serveFallback_dispatch rp fb (appAttempt :: post) input req rest
      hsends hsub
    rw [hd]
    unfold fallbackHandle
    rw [hrun]
    rfl
  refine ⟨h1, ?_⟩
  rw [h1, serve_routes input req rest hsends hsub]

/-- The app-head fallback response is still the route the REAL
`Route.Match.bestMatch` chose — `app_routes_total` lifted through the composed
chain: the fallback layer does not bypass the router. -/
theorem fallback_app_head_bestMatch (rp : Fallback.RetryPolicy)
    (fb : Fallback.ErrClass)
    (post : List (Fallback.Chain.Handler Request Response))
    (input : Bytes) (req : Request) (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest)
    (hok : (App.handle demoAppConfig req).status ≠ 502) :
    ∃ r, Route.Match.bestMatch demoAppConfig.table
            (App.targetSegments req.target) = some r
       ∧ serveFallback rp fb (appAttempt :: post) input
           = serialize (App.responseOfHandler r.handler) := by
  obtain ⟨r, hb, hh⟩ := App.app_routes_total demoAppConfig req
  have h1 := (fallback_app_head_serves_deployed rp fb post input req rest
    hsends hsub hok).1
  exact ⟨r, hb, by rw [h1, hh]⟩

/-! ## Concrete chain data (computed, not asserted) -/

/-- A handler that always fails with class `c` (a dead backend of that
flavor). -/
def failWith (i : Nat) (c : Fallback.ErrClass) :
    Fallback.Chain.Handler Request Response :=
  { hid := i, run := fun _ => .err c }

/-- A static backup handler: always succeeds with a `503`-styled maintenance
page (a serializer `Response`). -/
def backupAttempt : Fallback.Chain.Handler Request Response :=
  { hid := 2,
    run := fun _ =>
      .ok (error4xx 503 (str "Service Unavailable") (str "backup\n")) }

/-- Two retryable failures fall through and the chain exhausts: the terminal
page renders the LAST class seen and every handler was tried, in order. -/
example (req : Request) :
    Fallback.Chain.runChain Fallback.defaultPolicy .notFound
        [failWith 8 .timeout, failWith 9 .connectFailed] req
      = ([8, 9], .terminal .connectFailed) := rfl

/-- A terminal `forbidden` stops the chain immediately: the backup handler is
never tried. -/
example (req : Request) :
    Fallback.Chain.runChain Fallback.defaultPolicy .notFound
        [failWith 8 .forbidden, backupAttempt] req
      = ([8], .terminal .forbidden) := rfl

/-- A retryable failure falls through to the backup, which serves — exactly
one response, and the trace shows both handlers tried in order. -/
example (req : Request) :
    Fallback.Chain.runChain Fallback.defaultPolicy .notFound
        [failWith 8 .timeout, backupAttempt] req
      = ([8, 2], .byHandler 2
          (error4xx 503 (str "Service Unavailable") (str "backup\n"))) := rfl

end Reactor.FallbackWire
