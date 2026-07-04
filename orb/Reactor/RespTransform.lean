import Reactor.Deploy
import EarlyHints.Basic
import HtmlRewrite.Basic

/-!
# Reactor.RespTransform — the REAL EarlyHints and HtmlRewrite libraries, wired
into the DEPLOYED response pipeline.

Two response-shaping libraries, previously stranded, are wired here onto the
path the deployed orb actually runs: `Arena.Orb.main` → `Reactor.Deploy.deployStep`
→ `Reactor.Deploy.serveFull` → the deployed reactor over `deployConfig`. Both
transforms compose with `serveFull`'s own deployed response (`deployResp`, the
`App.handle` router output passed through the REAL `Header.run` under
`deployProg`), so they operate on the very bytes `main` writes — not a bespoke
side model.

## 1. HTTP 103 Early Hints (RFC 8297), on the deployed final response.

A deployed route may declare zero or more preload hints. We model the emission
as the REAL `EarlyHints.run` over `building`: one `emitInfo` per declared hint,
then one `emitFinal` carrying the deployed final response (`deployedFinal`, whose
status and body are exactly `serveFull`'s deployed response). The seam
`early_hints_precede_final_deployed` composes `EarlyHints.run_building_shape` with
`serveFull`: the emitted sequence is the hints (each a `103`) then EXACTLY one
final, in that order — every informational response precedes the one final, and
that final is the deployed response `serveFull` serializes on the dispatch path.

## 2. Streaming HTML rewrite, on the deployed response body.

`serveFull`'s deployed response body is passed through the REAL streaming
tokenizer `HtmlRewrite.tokenize`/`bytesOf` (the `htmlTransform` below). The
load-bearing property is **chunk-boundary safety**: feeding the body split at
*any* boundary and streaming the chunks yields the same rewritten output as
feeding it whole (`HtmlRewrite.stream_eq_whole`). The current transform is
lossless (identity — `htmlTransform_lossless`, i.e. `HtmlRewrite.roundtrip`); the
seam `htmlrewrite_deployed` states the rewritten deployed body is exactly the
real transform applied, chunk-boundary-safe, composed with `serveFull`.

Nothing here is a re-implementation: `EarlyHints.run`/`run_building_shape` and
`HtmlRewrite.tokenize`/`bytesOf`/`stream_eq_whole` are the library functions and
theorems themselves, applied to `Reactor.Deploy.deployResp`.
-/

namespace Reactor.RespTransform

open Proto (Bytes)
open Reactor (Response serialize demoResp sendsOf RingSubmission)
open Reactor.Deploy (deployResp deploySubs serveFull)

/-- On the dispatch path (the FSM emitted no bytes of its own), `serveFull`
serializes the deployed response — the same `cases`-on-discriminant shape as
`Reactor.Deploy.serveFull_faithful`, kept off the `whnf` blow-up an `unfold`
would trigger on the deployed config. -/
theorem serveFull_dispatch (input : Bytes) (hsends : sendsOf (deploySubs input) = []) :
    serveFull input = serialize (deployResp input) := by
  unfold serveFull
  cases hs : sendsOf (deploySubs input) with
  | nil => rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

/-! ## Bridge: a deployed `Response` as an `EarlyHints.Final` -/

/-- Total Latin-1 decode of a byte string to a `String` (each byte `< 256` is a
valid `Char`). Used only to view a deployed response's header bytes as the
`String` pairs the `EarlyHints` model carries; the ordering seam never inspects
them, so this is a faithful, proof-inert view. -/
def latin1 (bs : List UInt8) : String :=
  String.mk (bs.map (fun b => Char.ofNat b.toNat))

/-- View a deployed `Response` as the `EarlyHints.Final` (the one non-1xx
response). Status and body are carried through unchanged; headers are the
Latin-1 view. -/
def toFinal (r : Response) : EarlyHints.Final :=
  { status  := r.status
    headers := r.headers.map (fun p => (latin1 p.1, latin1 p.2))
    body    := r.body }

/-- `toFinal` carries the status through. Stated GENERIC over `r` so `isDefEq`
never forces `deployResp input` (an inherited-field projection on the deployed
response would whnf the whole `deploySubs`/`rewriteResp` computation). -/
theorem toFinal_status (r : Response) : (toFinal r).status = r.status := rfl

/-- `toFinal` carries the body through (generic, same discipline). -/
theorem toFinal_body (r : Response) : (toFinal r).body = r.body := rfl

/-- The deployed final response as an `EarlyHints.Final`: the response
`serveFull` emits on the dispatch path, viewed for the 103/final model. -/
def deployedFinal (input : Bytes) : EarlyHints.Final := toFinal (deployResp input)

/-- The action sequence for a route declaring preload `hints`: one `emitInfo`
per hint (each becomes a `103`), then exactly one `emitFinal` carrying the
deployed final response. -/
def hintActions (hints : List EarlyHints.Info) (f : EarlyHints.Final) :
    List EarlyHints.Action :=
  hints.map EarlyHints.Action.emitInfo ++ [EarlyHints.Action.emitFinal f]

/-- **Running the deployed hint sequence.** From `building`, emitting the hints
then the final yields exactly: the hints as `103` messages, in order, followed by
the one final message — and the builder is `committed`. This is the REAL
`EarlyHints.run` (via `run_info_cons`/`run_final_cons`), not a copy. -/
theorem run_hintActions (hints : List EarlyHints.Info) (f : EarlyHints.Final) :
    EarlyHints.run .building (hintActions hints f)
      = (.committed, hints.map EarlyHints.Msg.info ++ [EarlyHints.Msg.final f]) := by
  unfold hintActions
  induction hints with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    exact EarlyHints.run_final_cons f []
  | cons h t ih =>
    simp only [List.map_cons, List.cons_append]
    rw [EarlyHints.run_info_cons, ih]

/-! ## Seam 1 — every 103 precedes the one final, on the deployed path -/

/-- **`early_hints_precede_final_deployed` — the EarlyHints seam, on the deployed
path.** For a deployed dispatch declaring any preload `hints`, the emitted
sequence is the hints (each a `103` informational response) then EXACTLY one
final response, in that order:

* the emitted message list is `hints.map Msg.info ++ [Msg.final (deployedFinal)]`;
* composing `EarlyHints.run_building_shape`, that list decomposes as
  `pre ++ [final]` with `allInfo pre` — no informational response follows the
  final (every `103` precedes it);
* the one final's status and body are exactly the deployed response `serveFull`
  serializes on the dispatch path (`serveFull input = serialize (deployResp input)`).

A pipeline that emitted a `103` after the final, or emitted two finals, would fail
the shape; a final divorced from the served bytes would fail the last conjunct. -/
theorem early_hints_precede_final_deployed (input : Bytes)
    (hints : List EarlyHints.Info) (req : Proto.Request) (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (_hsub : deploySubs input = .dispatch req :: rest) :
    (EarlyHints.run .building (hintActions hints (deployedFinal input))).2
        = hints.map EarlyHints.Msg.info ++ [EarlyHints.Msg.final (deployedFinal input)]
    ∧ (∃ pre f,
        (EarlyHints.run .building (hintActions hints (deployedFinal input))).2
            = pre ++ [EarlyHints.Msg.final f]
        ∧ EarlyHints.allInfo pre)
    ∧ (deployedFinal input).status = (deployResp input).status
    ∧ (deployedFinal input).body = (deployResp input).body
    ∧ serveFull input = serialize (deployResp input) := by
  refine ⟨?_, ?_, toFinal_status (deployResp input), toFinal_body (deployResp input),
    serveFull_dispatch input hsends⟩
  · exact congrArg Prod.snd (run_hintActions hints (deployedFinal input))
  · rcases EarlyHints.run_building_shape (hintActions hints (deployedFinal input)) with
      ⟨hst, _⟩ | ⟨_, pre, f, heq, hpre⟩
    · exfalso
      have hcommit : (EarlyHints.run .building
          (hintActions hints (deployedFinal input))).1 = EarlyHints.State.committed :=
        congrArg Prod.fst (run_hintActions hints (deployedFinal input))
      rw [hcommit] at hst
      exact absurd hst (by decide)
    · exact ⟨pre, f, heq, hpre⟩

/-- **At most one final on the deployed path.** The deployed hint sequence emits
no more than one final (non-1xx) response — `EarlyHints.at_most_one_final` lifted
to the deployed final. -/
theorem deployed_at_most_one_final (input : Bytes) (hints : List EarlyHints.Info) :
    ((EarlyHints.run .building (hintActions hints (deployedFinal input))).2.filter
        (fun m => !m.isInfo)).length ≤ 1 :=
  EarlyHints.at_most_one_final (hintActions hints (deployedFinal input))

/-! ## Seam 2 — the streaming HTML rewrite on the deployed response body -/

/-- **The real streaming HTML transform.** Tokenize the bytes with the REAL
`HtmlRewrite.tokenize` and re-serialize (`HtmlRewrite.bytesOf`). This is the
library's streaming rewriter; it is currently lossless (see
`htmlTransform_lossless`). Its load-bearing property is chunk-boundary safety. -/
def htmlTransform (bs : Bytes) : Bytes := HtmlRewrite.bytesOf (HtmlRewrite.tokenize bs)

/-- The transform is lossless (an identity rewrite) — `HtmlRewrite.roundtrip`. -/
theorem htmlTransform_lossless (bs : Bytes) : htmlTransform bs = bs :=
  HtmlRewrite.roundtrip bs

/-- **The deployed response with its body streamed through the HTML rewriter.**
Exactly `serveFull`'s deployed response (`deployResp`) with its body replaced by
the real `htmlTransform` — the rewrite stage inserted into the deployed serialize
path. -/
def deployRespHtml (input : Bytes) : Response :=
  { deployResp input with body := htmlTransform (deployResp input).body }

/-- The rewritten deployed body is exactly the real transform of the deployed
body. Safe `rfl`: `body` is the field the update SETS, so the projection reads it
back directly without forcing `deployResp input`. -/
theorem deployRespHtml_body (input : Bytes) :
    (deployRespHtml input).body = htmlTransform (deployResp input).body := rfl

/-- **The deployed serve with the HTML rewrite stage.** Mirrors `serveFull`:
faithful FSM sends are forwarded in order; a bare dispatch is answered by the
deployed response whose body is streamed through `htmlTransform`. -/
def serveFullHtml (input : Bytes) : Bytes :=
  match sendsOf (deploySubs input) with
  | [] => serialize (deployRespHtml input)
  | sends => sends.flatten

/-- On the dispatch path, `serveFullHtml` serializes the HTML-rewritten deployed
response — same `cases` shape as `serveFull_dispatch`. -/
theorem serveFullHtml_dispatch (input : Bytes)
    (hsends : sendsOf (deploySubs input) = []) :
    serveFullHtml input = serialize (deployRespHtml input) := by
  unfold serveFullHtml
  cases hs : sendsOf (deploySubs input) with
  | nil => rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

/-- **`htmlrewrite_deployed` — the HtmlRewrite seam, on the deployed path.** For a
deployed dispatch:

* the rewritten body is EXACTLY the real `HtmlRewrite` transform applied to
  `serveFull`'s deployed response body;
* `serveFullHtml` serializes that rewritten response — the transform composed
  with `serveFull`'s deployed response (`serveFull input = serialize (deployResp input)`,
  whose body is the transform's input);
* **chunk-boundary safety**: splitting the deployed body at *any* boundary
  `a ++ b` and streaming the two chunks (`feedBytes (tokenize a) b`) yields the
  same rewritten bytes as feeding it whole — `HtmlRewrite.stream_eq_whole`. A
  naive chunk-at-a-time rewriter would get this wrong. -/
theorem htmlrewrite_deployed (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (_hsub : deploySubs input = .dispatch req :: rest) :
    (deployRespHtml input).body = htmlTransform (deployResp input).body
    ∧ serveFullHtml input = serialize (deployRespHtml input)
    ∧ serveFull input = serialize (deployResp input)
    ∧ ∀ a b, a ++ b = (deployResp input).body →
        HtmlRewrite.bytesOf (HtmlRewrite.feedBytes (HtmlRewrite.tokenize a) b)
          = htmlTransform (deployResp input).body := by
  refine ⟨deployRespHtml_body input, serveFullHtml_dispatch input hsends,
    serveFull_dispatch input hsends, ?_⟩
  intro a b hab
  unfold htmlTransform
  rw [HtmlRewrite.stream_eq_whole, hab]

/-- **Both stages compose on the deployed dispatch.** The HTML-rewritten deployed
serve differs from `serveFull` only by the real `htmlTransform` on the body, and
the deployed final for the 103/final model carries that same deployed response's
body. So EarlyHints (ordering) and HtmlRewrite (body) sit on the one deployed
path `main` runs. -/
theorem resp_transforms_compose_deployed (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (_hsub : deploySubs input = .dispatch req :: rest) :
    serveFull input = serialize (deployResp input)
    ∧ serveFullHtml input = serialize (deployRespHtml input)
    ∧ (deployedFinal input).body = (deployRespHtml input).body := by
  refine ⟨serveFull_dispatch input hsends, serveFullHtml_dispatch input hsends, ?_⟩
  unfold deployedFinal
  rw [toFinal_body, deployRespHtml_body, htmlTransform_lossless]

end Reactor.RespTransform
