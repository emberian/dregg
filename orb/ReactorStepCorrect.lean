/-
Reactor core step — the *correctness* theory for the HTTP/1.1 dispatch path.

The reactor step (`Reactor.step`) is a total function: safety results say it
never gets stuck and recycles each received buffer exactly once
(`Reactor.recv_recycles_exactly_once`). Totality and buffer discipline say
nothing about *which request* the reactor hands to the application. A degenerate
reactor that dispatched a fixed empty request on every input would satisfy every
safety obligation while dispatching total nonsense.

This file states and proves the CORRECTNESS successor: on a well-formed HTTP/1.1
request datagram the reactor dispatches the request whose method and target are
*exactly* the bytes the input encodes, per the RFC 9112 request-line grammar

    request-line = method SP request-target SP HTTP-version

(RFC 9112 §3). The specification `specDispatch` is written directly from that
grammar as a byte-splitting function on the input — the method is the run of
bytes up to the first SP, the target is the run of bytes up to the next SP after
it — with NO reference to the reactor, the connection FSM, or the arena parser.
The refinement theorem `step_dispatch_correct` then proves the reactor's actual
dispatched request agrees with this independent specification on method and
target.

Non-vacuity: the specification is genuine byte extraction (`takeWhile`/`take` on
the SP separator), while the implementation extracts its fields through an arena
`Store`/`Entry`/`resolve` indirection — two different definitions, proven equal.
A reactor that dispatched an empty request, or the wrong field, fails the
`d.method = (specDispatch input).method` equation because for any real request
line the method run before the first SP is non-empty.

Scope: method and target agreement are proved end-to-end (composing the
request-line field-exactness of `parse_reqline_sound`). Version agreement and
the header-map agreement are named UNCLOSED — the version field's independent
specification requires pinning the request-line terminator (the first CRLF, which
a lone CR inside the field does not terminate), and the header-block round-trip
is itself UNCLOSED in the parser soundness theory this builds on.
-/
import Reactor.Config
import Reactor.Contract
import ArenaSound

open Arena.Parse (SP CR)

namespace Reactor
namespace StepCorrect

open Proto (Bytes Request)

/-! ## The RFC 9112 request-line specification (independent of the implementation)

`request-line = method SP request-target SP HTTP-version` (RFC 9112 §3). The
method is the maximal run of bytes before the first SP; the request-target is the
maximal run of bytes before the next SP after the method's separator; the
HTTP-version is the remainder of the request line. These are byte-level
splitting functions on the raw input — they never mention `Proto.step`,
`Reactor.step`, or `Arena.Parse.parse`. -/

/-- The request method: the run of input bytes up to the first SP (RFC 9112 §3,
`method` token). -/
def specMethod (input : Bytes) : Bytes := input.takeWhile (· != SP)

/-- The request-target: the run of bytes up to the next SP, after dropping the
method and its SP separator (RFC 9112 §3, `request-target` token). -/
def specTarget (input : Bytes) : Bytes :=
  (input.drop ((specMethod input).length + 1)).takeWhile (· != SP)

/-- The HTTP-version: the remainder of the request line up to its CRLF, after the
target and its SP separator (RFC 9112 §3, `HTTP-version` token). Stated here to
complete the request-line specification; version agreement is UNCLOSED. -/
def specVersion (input : Bytes) : Bytes :=
  let afterM := input.drop ((specMethod input).length + 1)
  let afterT := afterM.drop ((afterM.takeWhile (· != SP)).length + 1)
  afterT.takeWhile (· != CR)

/-- **The specification.** The `Proto.Request` the RFC 9112 request-line grammar
dictates for a well-formed request datagram: method, target, and version are the
grammar tokens read directly off the input bytes. The header map is left empty
here — its agreement is UNCLOSED (see the module comment). -/
def specDispatch (input : Bytes) : Request :=
  { method  := specMethod input
    target  := specTarget input
    version := specVersion input
    headers := [] }

/-! ## A separator lemma: `takeWhile (≠ c)` cuts exactly at the first `c`

If `c` occurs at index `i` and nowhere earlier, then the maximal run of
non-`c` bytes is exactly the first `i` bytes. This is the bridge from the arena
parser's index-based field boundaries to the specification's `takeWhile` form. -/

theorem takeWhile_ne_eq_take {c : UInt8} :
    ∀ {l : Bytes} {i : Nat}, l[i]? = some c →
      (∀ j, j < i → l[j]? ≠ some c) → l.takeWhile (· != c) = l.take i
  | [], i, hi, _ => by simp at hi
  | x :: xs, 0, hi, _ => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp [List.takeWhile_cons]
  | x :: xs, i + 1, hi, hb => by
      have hx : x ≠ c := by
        have h0 := hb 0 (Nat.succ_pos i)
        simp only [List.getElem?_cons_zero, ne_eq, Option.some.injEq] at h0
        exact h0
      have hi' : xs[i]? = some c := by
        simpa using hi
      have hb' : ∀ j, j < i → xs[j]? ≠ some c := by
        intro j hj
        have := hb (j + 1) (by omega)
        simpa using this
      rw [List.takeWhile_cons]
      simp only [bne_iff_ne.mpr hx, if_true]
      rw [takeWhile_ne_eq_take hi' hb', List.take_succ_cons]

/-! ## The reactor reduces to a dispatch of the resolved request

On a fresh plain HTTP/1.1 connection, a `recvInto` carrying a well-formed request
head runs `Proto.step` down `onBytes → runH1 → h1Loop`, whose first output is a
`dispatch` of the parser's resolved request. The reactor translates that faithfully
(`ofOutput (.dispatch r) = .dispatch r`) into its submission list. -/

/-- The connection FSM emits the resolved request as the head of its outputs. -/
theorem onBytes_head_dispatch (input : Bytes) (req : Arena.Parse.Request)
    (hfit : input.length ≤ Reactor.Config.demoConfig.maxHeaderBytes)
    (hne : input ≠ [])
    (hwf : Arena.Parse.parse input = .complete req) :
    ∃ rest, (Proto.onBytes Reactor.Config.demoConfig (.plainH1 []) input).outs
        = Proto.Output.dispatch (Reactor.Config.protoReqOf req) :: rest := by
  have hparse := Reactor.Config.demoConfig_complete_content input req hwf
  have hEmpty : input.isEmpty = false := by
    cases input with
    | nil => exact absurd rfl hne
    | cons a as => rfl
  -- `onBytes` on a fresh plain-H1 state is `runH1` on the input (no accumulation)
  show ∃ rest, (Proto.runH1 Reactor.Config.demoConfig .plainH1 ([] ++ input) []).outs
      = _ :: rest
  rw [List.nil_append]
  unfold Proto.runH1
  rw [if_neg (by simp only [gt_iff_lt, Nat.not_lt]; exact hfit)]
  -- reduce `h1Loop` one step: nonempty buffer, parse is `.request …`
  have hfuel : input.length + 1 = (input.length) + 1 := rfl
  simp only []
  -- unfold the loop body at fuel = input.length + 1
  show ∃ rest, ([] ++ (Proto.h1Loop Reactor.Config.demoConfig (input.length + 1) input).outs)
      = _ :: rest
  rw [List.nil_append]
  unfold Proto.h1Loop
  rw [if_neg (by simpa using hEmpty)]
  rw [hparse]
  dsimp only
  -- both keep-alive branches lead with `.dispatch (protoReqOf req)`
  by_cases hka : Reactor.Config.deriveKeepAlive (Reactor.Config.protoReqOf req).headers = true
  · rw [if_pos hka]
    exact ⟨_, rfl⟩
  · rw [if_neg hka]
    exact ⟨[], rfl⟩

/-- The reactor's submission list contains the dispatch of the resolved request. -/
theorem step_dispatches_resolved (input : Bytes) (bid : Uring.Bid)
    (req : Arena.Parse.Request)
    (hfit : input.length ≤ Reactor.Config.demoConfig.maxHeaderBytes)
    (hne : input ≠ [])
    (hwf : Arena.Parse.parse input = .complete req) :
    RingSubmission.dispatch (Reactor.Config.protoReqOf req)
      ∈ (Reactor.step Reactor.Config.demoConfig (.active Proto.Conn.mkPlain)
          (.recvInto bid input)).2 := by
  obtain ⟨rest, hout⟩ := onBytes_head_dispatch input req hfit hne hwf
  -- `Proto.step` on `bytesReceived` runs `finish` over `onBytes`
  have hmem : Proto.Output.dispatch (Reactor.Config.protoReqOf req)
      ∈ (Proto.step Reactor.Config.demoConfig (.active Proto.Conn.mkPlain)
          (.bytesReceived input)).2 := by
    show Proto.Output.dispatch (Reactor.Config.protoReqOf req)
        ∈ (Proto.finish Proto.Conn.mkPlain
            (Proto.onBytes Reactor.Config.demoConfig (.plainH1 []) input)).2
    unfold Proto.finish Proto.gate
    -- `Conn.mkPlain.sendBlocked = false`: sends pass through unchanged
    simp only [Proto.Conn.mkPlain, Bool.false_eq_true, if_neg, if_false]
    rw [hout]
    by_cases hc : (Proto.onBytes Reactor.Config.demoConfig (.plainH1 []) input).closeNow = true
    · rw [if_pos hc]; simp
    · rw [if_neg hc]; simp
  -- lift through the reactor translation
  show RingSubmission.dispatch (Reactor.Config.protoReqOf req)
      ∈ ((Proto.step Reactor.Config.demoConfig (.active Proto.Conn.mkPlain)
          (toInput (.recvInto bid input))).2.map ofOutput ++ _)
  apply List.mem_append_left
  have : ofOutput (Proto.Output.dispatch (Reactor.Config.protoReqOf req))
      = RingSubmission.dispatch (Reactor.Config.protoReqOf req) := rfl
  rw [← this]
  exact List.mem_map_of_mem _ hmem

/-! ## The refinement theorem: the reactor dispatches the RFC-specified request -/

/-- **`step_dispatch_correct` — reactor dispatch is correct.** On a fresh plain
HTTP/1.1 connection, when the received datagram `input` is a well-formed request
head (the arena parser reports `complete`) that fits the header buffer, the
reactor's submission list contains a `dispatch d` whose method and target are
*exactly* the RFC 9112 request-line fields the input encodes — `d.method =
specMethod input` and `d.target = specTarget input`, where `specMethod`/`specTarget`
are byte-splitting functions on the input alone, defined with no reference to the
implementation.

This is the meaning successor to the safety results: the reactor does not merely
dispatch *a* well-formed request, it dispatches the *right* one. A reactor that
dispatched a fixed/empty request, or swapped method for target, fails the
equalities (`specMethod` of any real request line is the non-empty method token).

UNCLOSED: version-field agreement and header-map agreement (see the module
comment). -/
theorem step_dispatch_correct (input : Bytes) (bid : Uring.Bid)
    (req : Arena.Parse.Request)
    (hfit : input.length ≤ Reactor.Config.demoConfig.maxHeaderBytes)
    (hwf : Arena.Parse.parse input = .complete req) :
    ∃ d : Request,
      RingSubmission.dispatch d
        ∈ (Reactor.step Reactor.Config.demoConfig (.active Proto.Conn.mkPlain)
            (.recvInto bid input)).2
      ∧ d.method = (specDispatch input).method
      ∧ d.target = (specDispatch input).target := by
  -- field-exactness of the request line from the parser soundness theory
  obtain ⟨i₁, i₂, L, hi1L, hi12L, hLlen, hsp1, hsp2, hnb1, hnb2,
      ⟨mb, hmres, hmeq⟩, ⟨tb, htres, hteq⟩, _hver, _hser⟩ :=
    Arena.Parse.parse_reqline_sound hwf
  -- input is non-empty (`i₁ < L ≤ input.length`)
  have hne : input ≠ [] := by
    intro h; rw [h] at hLlen; simp at hLlen; omega
  refine ⟨Reactor.Config.protoReqOf req, step_dispatches_resolved input bid req hfit hne hwf, ?_, ?_⟩
  · -- method agreement
    show Reactor.Config.resolveBytes req.store req.method = specMethod input
    unfold Reactor.Config.resolveBytes specMethod
    rw [hmres]; dsimp only; rw [hmeq]
    exact (takeWhile_ne_eq_take hsp1 hnb1).symm
  · -- target agreement
    show Reactor.Config.resolveBytes req.store req.target = specTarget input
    unfold Reactor.Config.resolveBytes specTarget
    rw [htres]; dsimp only; rw [hteq]
    -- the method token has length `i₁`, so the target drop offset is `i₁ + 1`
    have hmlen : (specMethod input).length = i₁ := by
      unfold specMethod
      rw [takeWhile_ne_eq_take hsp1 hnb1, List.length_take]
      omega
    rw [hmlen]
    -- shift the SP facts into the `input.drop (i₁ + 1)` frame and apply the lemma
    have hd1 : (input.drop (i₁ + 1))[i₂]? = some SP := by
      rw [List.getElem?_drop]; exact hsp2
    have hd2 : ∀ j, j < i₂ → (input.drop (i₁ + 1))[j]? ≠ some SP := by
      intro j hj
      rw [List.getElem?_drop]
      exact hnb2 (i₁ + 1 + j) (by omega) (by omega)
    exact (takeWhile_ne_eq_take hd1 hd2).symm

end StepCorrect
end Reactor
