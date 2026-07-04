import Reactor.Serve
import Reactor.Deploy

/-!
# Reactor.Bridge — the deployed reactor and the test reactor agree on HTTP/1.1

`Reactor.Serve.reactorSubs` runs the proven reactor over `demoConfig`; every
island lane (App routing, keep-alive, rate, SSE, …) proved its seam theorem as a
property of `reactorSubs input` / `serve input`. `Reactor.Deploy.deploySubs` runs
the *same* reactor over `deployConfig` — `demoConfig` with the three codec lanes
(TLS, WebSocket, SOCKS) replaced by their real engines through the lanes' own
`{ cfg with … }` transformers (`wireTls`/`wireWs`/`wireSocks`).

The deployed binary (`Arena.Orb.main` → `Deploy.deployStep` → `serveFull` →
`Reactor.step deployConfig`) therefore runs on `deployConfig`, not `demoConfig`.
For the island seams to count on the deployed path we must connect the two.

The connection is exact on the HTTP/1.1 plaintext path. The initial connection
state is `Conn.mkPlain`, whose protocol state is `.plainH1 []`. On a `recvInto`
completion the reactor runs `Proto.step … (.bytesReceived data)`, which for a
`.plainH1` state is `onBytes cfg (.plainH1 …) data = runH1 cfg .plainH1 …` — and
`runH1`/`h1Loop` read **only** four `Config` fields:

* `maxHeaderBytes` (the oversize gate),
* `h1Parse` (the arena parser),
* `oversizeResponse` (the canned 431),
* `errorResponse` (the canned 400).

None of these is a codec field. The three wire transformers are structure updates
that set *only* the codec fields (`hsFeed`/`tlsRecv`/`tlsSend`, `wsFeed`/`wsEncode`,
`socksFeed`), so each of the four HTTP/1.1-read fields is *definitionally* equal
between `deployConfig` and `demoConfig`. Hence `Proto.step` — and the whole
`Reactor.step` around it — reduces to the identical result on either config:
`deploySubs_eq_reactorSubs` holds by `rfl`.

The corollary `lift` transports any property `P` of `reactorSubs input` onto
`deploySubs input`, so every island seam already proven over the test reactor
lifts, for free, onto the submissions the deployed orb actually acts on.
-/

namespace Reactor
namespace Bridge

open Proto (Bytes)

/-! ## The four HTTP/1.1-read fields agree between the two configs

These are the *only* `Proto.Config` fields the `.plainH1` arm of `onBytes`
(`runH1` → `h1Loop`) ever reads. Each holds by `rfl` because the wire
transformers touch only codec fields; recorded explicitly so the argument is
auditable field-by-field, not just a black-box `rfl` on the whole step. -/

theorem deployConfig_h1Parse :
    Reactor.Deploy.deployConfig.h1Parse = Reactor.Config.demoConfig.h1Parse := rfl

theorem deployConfig_maxHeaderBytes :
    Reactor.Deploy.deployConfig.maxHeaderBytes = Reactor.Config.demoConfig.maxHeaderBytes :=
  rfl

theorem deployConfig_oversizeResponse :
    Reactor.Deploy.deployConfig.oversizeResponse
      = Reactor.Config.demoConfig.oversizeResponse := rfl

theorem deployConfig_errorResponse :
    Reactor.Deploy.deployConfig.errorResponse
      = Reactor.Config.demoConfig.errorResponse := rfl

/-! ## The congruence on the plainH1 arm

A full `rfl` on the whole step does **not** go through: `h1Loop` recurses under a
symbolic fuel (`buf.length + 1`), so the recursion is stuck and carries the
*entire* config value — and `deployConfig ≠ demoConfig` as whole structures (the
codec fields differ). The projections the path actually reads are defeq (the four
lemmas above), so we lift that field-wise agreement up through `h1Loop → runH1 →
onBytes → Proto.step → Reactor.step` by explicit congruence. -/

/-- `h1Loop` reads the config only through `h1Parse` and `errorResponse` (both
defeq across the two configs) and its own recursion. By induction on the fuel the
two configs give the identical loop result. -/
theorem h1Loop_eq (fuel : Nat) (buf : Bytes) :
    Proto.h1Loop Reactor.Deploy.deployConfig fuel buf
      = Proto.h1Loop Reactor.Config.demoConfig fuel buf := by
  induction fuel generalizing buf with
  | zero => rfl
  | succ n ih =>
    simp only [Proto.h1Loop]
    rw [deployConfig_h1Parse, deployConfig_errorResponse]
    split
    · rfl
    · split
      · rfl
      · rfl
      · rfl
      · split
        · rw [ih]
        · rfl

/-- `runH1` reads the config through `maxHeaderBytes`, `oversizeResponse`, and
`h1Loop` — all agreeing across the two configs — so it gives the identical
effect. -/
theorem runH1_eq (frame : Bytes → Proto.ProtoState) (buf : Bytes)
    (pre : List Proto.Output) :
    Proto.runH1 Reactor.Deploy.deployConfig frame buf pre
      = Proto.runH1 Reactor.Config.demoConfig frame buf pre := by
  unfold Proto.runH1
  rw [deployConfig_maxHeaderBytes, deployConfig_oversizeResponse, h1Loop_eq]

/-- The `.plainH1` arm of `onBytes` is `runH1`, which is config-agnostic on the
read fields. -/
theorem onBytes_plainH1_eq (b data : Bytes) :
    Proto.onBytes Reactor.Deploy.deployConfig (.plainH1 b) data
      = Proto.onBytes Reactor.Config.demoConfig (.plainH1 b) data := by
  show Proto.runH1 Reactor.Deploy.deployConfig .plainH1 (b ++ data) []
     = Proto.runH1 Reactor.Config.demoConfig .plainH1 (b ++ data) []
  exact runH1_eq _ _ _

/-- `Proto.step` on a fresh plain connection receiving bytes is `finish mkPlain`
applied to the `.plainH1` `onBytes` effect — so the two configs step identically.
`Conn.mkPlain.proto` is `.plainH1 []`. -/
theorem protoStep_eq (input : Bytes) :
    Proto.step Reactor.Deploy.deployConfig (.active Proto.Conn.mkPlain)
        (.bytesReceived input)
      = Proto.step Reactor.Config.demoConfig (.active Proto.Conn.mkPlain)
        (.bytesReceived input) := by
  show Proto.finish Proto.Conn.mkPlain
        (Proto.onBytes Reactor.Deploy.deployConfig (.plainH1 []) input)
     = Proto.finish Proto.Conn.mkPlain
        (Proto.onBytes Reactor.Config.demoConfig (.plainH1 []) input)
  rw [onBytes_plainH1_eq]

/-- **The two reactors agree on the plainH1 recv path.** Feeding `input` as one
`recvInto` completion to the deployed reactor from a fresh plain connection
produces exactly the submissions the test reactor (`reactorSubs`) produces. The
`Reactor.step` wrapper is a pure function of the inner `Proto.step` result
(translate every output, then append the buffer recycle), so `protoStep_eq`
lifts through it. -/
theorem deploySubs_eq_reactorSubs (input : Bytes) :
    Reactor.Deploy.deploySubs input = Reactor.reactorSubs input := by
  show ((Proto.step Reactor.Deploy.deployConfig (.active Proto.Conn.mkPlain)
            (.bytesReceived input)).2.map Reactor.ofOutput
          ++ [RingSubmission.recycleBuffer 0])
     = ((Proto.step Reactor.Config.demoConfig (.active Proto.Conn.mkPlain)
            (.bytesReceived input)).2.map Reactor.ofOutput
          ++ [RingSubmission.recycleBuffer 0])
  rw [protoStep_eq]

/-- **The lift.** Any property `P` that holds of the test reactor's submissions
holds of the deployed reactor's submissions, on the plainH1 recv path. This is
the transport lemma: an island lane proves `P (reactorSubs input)` once, and the
same fact lands on `deploySubs input` — the submissions the deployed orb
(`serveFull` / `deployStep`, what `main` runs) acts on. -/
theorem lift {P : List RingSubmission → Prop} (input : Bytes)
    (h : P (Reactor.reactorSubs input)) : P (Reactor.Deploy.deploySubs input) := by
  rw [deploySubs_eq_reactorSubs]; exact h

/-- The lift in the other direction (the equality is symmetric): a property of
the deployed submissions is a property of the test submissions. Handy when a
deployed-path fact (e.g. from `Reactor.Deploy`) should be reused on `serve`. -/
theorem lift_symm {P : List RingSubmission → Prop} (input : Bytes)
    (h : P (Reactor.Deploy.deploySubs input)) : P (Reactor.reactorSubs input) := by
  rw [← deploySubs_eq_reactorSubs]; exact h

/-! ## Worked transports — island seams landed on the deployed path

Each theorem below is an existing `Reactor.Serve` seam, restated over
`deploySubs`/`serveFull` and proved *only* by rewriting along
`deploySubs_eq_reactorSubs`. They are here to demonstrate the lift is real, not
to re-prove anything: the mathematical content is entirely the `Serve`-side
theorem. -/

/-- `serve_routes` transported: on the deployed plainH1 path, a dispatched
request with no FSM send bytes is answered by the real application layer over
the same demo route table. (The deployed pipeline additionally rewrites headers;
this is the *pre-rewrite* routing content, lifted verbatim from the test view.) -/
theorem deployed_routes (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (Reactor.Deploy.deploySubs input) = [])
    (hsub : Reactor.Deploy.deploySubs input = .dispatch req :: rest) :
    Reactor.serve input = serialize (App.handle demoAppConfig req) := by
  have hsends' : sendsOf (Reactor.reactorSubs input) = [] := by
    rw [← deploySubs_eq_reactorSubs]; exact hsends
  have hsub' : Reactor.reactorSubs input = .dispatch req :: rest := by
    rw [← deploySubs_eq_reactorSubs]; exact hsub
  exact Reactor.serve_routes input req rest hsends' hsub'

/-- `serve_routes_bestMatch` transported: the route the served bytes reflect on a
deployed dispatch is the one the real `Route.Match.bestMatch` selected. -/
theorem deployed_routes_bestMatch (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (Reactor.Deploy.deploySubs input) = [])
    (hsub : Reactor.Deploy.deploySubs input = .dispatch req :: rest) :
    ∃ r, Route.Match.bestMatch demoAppConfig.table
            (App.targetSegments req.target) = some r
       ∧ Reactor.serve input = serialize (App.responseOfHandler r.handler) := by
  have hsends' : sendsOf (Reactor.reactorSubs input) = [] := by
    rw [← deploySubs_eq_reactorSubs]; exact hsends
  have hsub' : Reactor.reactorSubs input = .dispatch req :: rest := by
    rw [← deploySubs_eq_reactorSubs]; exact hsub
  exact Reactor.serve_routes_bestMatch input req rest hsends' hsub'

end Bridge
end Reactor
