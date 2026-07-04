import Tls.Theorems

/-!
# TLS 1.3 server handshake state machine — RFC 8446 conformance

This module upgrades the `Tls` handshake FSM (`Tls.stepPhase` / `Tls.step`,
`Tls/Step.lean`) from a safety artifact to a **correctness-by-refinement**
one against the state machine that RFC 8446 mandates for a TLS 1.3 server.

## The specification (independent, from the RFC)

`RfcState` and `RfcStep` below are an *independent* transcription of the
server state diagram in **RFC 8446, Appendix A.2 ("Server")** — the
diagram

```
   START --Recv ClientHello--> RECVD_CH --Select parameters--> NEGOTIATED
   RECVD_CH --Send HelloRetryRequest--> START
   NEGOTIATED --0-RTT--> WAIT_EOED --Recv EndOfEarlyData--> WAIT_FLIGHT2
   NEGOTIATED --No 0-RTT--> WAIT_FLIGHT2
   WAIT_FLIGHT2 --(No auth / client auth)--> WAIT_FINISHED
   WAIT_FINISHED --Recv Finished; K_recv = application--> CONNECTED
```

Crucially the RFC places the "Can send app data after here" marker at
`NEGOTIATED` for the *send* direction, but the **receive** direction only
switches to application keys on the `WAIT_FINISHED --Recv Finished-->
CONNECTED` edge: the server accepts full application data from the client
*only after the client's Finished is verified*. That is the property this
module pins.

`RfcStep` is written with **no reference to the implementation**: it names
what the RFC permits, edge by edge. The lemmas `rfc_connected_needs_finished`
and `rfc_no_backward_from_connected` prove the spec itself has the intended
shape (CONNECTED is entered only through the Finished edge, and there is no
edge back out of CONNECTED into the handshake), so the spec is not vacuous.

## The refinement (implementation ⊑ spec)

`absPhase : Tls.Phase → RfcState` reads each implementation phase as the
RFC state it represents. The three headline theorems are:

* `transition_agreement` — every implementation step moves the abstract
  state along a **path permitted by the RFC diagram** (`RfcReaches`, the
  reflexive-transitive closure of `RfcStep`). A step that ran an
  RFC-forbidden edge — e.g. reverting an established connection back into
  the handshake — is rejected, because `RfcReaches .connected _` reaches
  only `{connected, closed}`.

* `no_appdata_before_connected` — from any phase the abstraction reads as
  *not* CONNECTED, a step emits **no application-data output**
  (`sendPlain` / `deliverPlain`). 0.5-RTT early data (`deliverEarly`) is
  the RFC's separately-gated 0-RTT exception (RFC 8446 §2.3, §4.2.10; the
  `WAIT_EOED` branch) and is excluded from `isAppData` by design; it is
  itself gated on `earlyDataAccepted` by `Tls.early_data_needs_flag`.

* `connected_only_via_hsDone` — the abstract state becomes CONNECTED only
  on a `bytesReceived` step whose handshake engine reports `.done`, i.e.
  the RFC's "Recv Finished" event. This ties the abstract Finished edge to
  the one concrete transition that realizes it, so no implementation input
  other than a completing handshake can reach CONNECTED.

Non-vacuity witnesses (each theorem rejects a wrong FSM): an implementation
that entered `.estabUser` on `.peerClosed` fails `connected_only_via_hsDone`;
one that emitted `.deliverPlain` while `.handshaking` fails
`no_appdata_before_connected`; one with an `estabOffload → handshaking`
edge fails `transition_agreement`.
-/

namespace TlsRfc

open Tls

/-! ## The RFC 8446 Appendix A.2 server state machine (specification) -/

/-- The server states of the RFC 8446 Appendix A.2 diagram, plus a
terminal `closed` (a connection can always be torn down — the diagram
proper omits teardown, but a total transition relation must name it). -/
inductive RfcState
  /-- START — awaiting the ClientHello. -/
  | start
  /-- RECVD_CH — ClientHello received, parameters not yet selected. -/
  | recvdCh
  /-- NEGOTIATED — parameters selected; the server flight is sent, the
  server may now *send* application data (send-direction keys switch). -/
  | negotiated
  /-- WAIT_EOED — 0-RTT accepted; draining early data until EndOfEarlyData. -/
  | waitEoed
  /-- WAIT_FLIGHT2 — awaiting the client's second flight. -/
  | waitFlight2
  /-- WAIT_FINISHED — awaiting the client Finished. The receive direction
  is still on handshake keys here. -/
  | waitFinished
  /-- CONNECTED — client Finished verified; receive keys are application
  keys. Full application data may flow in both directions. -/
  | connected
  /-- Terminal. -/
  | closed
deriving Repr, DecidableEq

/-- The RFC-permitted single edges of the Appendix A.2 server diagram,
transcribed directly from the RFC. Every constructor is one labelled arrow
of that diagram (auth sub-states WAIT_CERT/WAIT_CV are collapsed into the
single `waitFlight2 → waitFinished` edge, exactly the "No auth" arrow). -/
inductive RfcStep : RfcState → RfcState → Prop
  /-- START --Recv ClientHello--> RECVD_CH. -/
  | recvClientHello : RfcStep .start .recvdCh
  /-- RECVD_CH --Send HelloRetryRequest--> START. -/
  | helloRetryRequest : RfcStep .recvdCh .start
  /-- RECVD_CH --Select parameters--> NEGOTIATED. -/
  | selectParameters : RfcStep .recvdCh .negotiated
  /-- NEGOTIATED --0-RTT--> WAIT_EOED. -/
  | sendFlightEarly : RfcStep .negotiated .waitEoed
  /-- NEGOTIATED --No 0-RTT--> WAIT_FLIGHT2. -/
  | sendFlight : RfcStep .negotiated .waitFlight2
  /-- WAIT_EOED --Recv EndOfEarlyData--> WAIT_FLIGHT2. -/
  | recvEndOfEarlyData : RfcStep .waitEoed .waitFlight2
  /-- WAIT_FLIGHT2 --(No auth / after WAIT_CERT..WAIT_CV)--> WAIT_FINISHED. -/
  | flight2Complete : RfcStep .waitFlight2 .waitFinished
  /-- WAIT_FINISHED --Recv Finished; K_recv = application--> CONNECTED.
  This is the *only* edge into CONNECTED. -/
  | recvFinished : RfcStep .waitFinished .connected
  /-- Teardown: any state may close (fatal alert / EOF / shutdown). -/
  | close (a : RfcState) : RfcStep a .closed

/-- Reflexive-transitive closure: an RFC-permitted *path* through the
diagram. The implementation collapses the handshake sub-path into an
opaque engine, so one implementation step corresponds to a path here
(a stuttering refinement). -/
inductive RfcReaches : RfcState → RfcState → Prop
  | refl (a : RfcState) : RfcReaches a a
  | tail {a b c : RfcState} (h : RfcReaches a b) (e : RfcStep b c) :
      RfcReaches a c

/-! ### Spec-side shape lemmas (the spec is non-vacuous on its own) -/

/-- CONNECTED is entered only through the Finished edge: the sole RFC
predecessor of CONNECTED is WAIT_FINISHED. This is the receive-direction
"K_recv = application only after Recv Finished" property, read off the
spec alone. -/
theorem rfc_connected_needs_finished {a : RfcState}
    (h : RfcStep a .connected) : a = .waitFinished := by
  cases h; rfl

/-- There is no RFC path out of CONNECTED back into the handshake: from
CONNECTED the reachable set is exactly `{connected, closed}`. So an
implementation cannot "un-connect". -/
theorem rfc_no_backward_from_connected {c : RfcState}
    (h : RfcReaches .connected c) : c = .connected ∨ c = .closed := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ e ih =>
    rcases ih with h | h
    · subst h; cases e; exact Or.inr rfl
    · subst h; cases e; exact Or.inr rfl

/-! ### Reachability helpers -/

theorem RfcReaches.single {a b : RfcState} (e : RfcStep a b) :
    RfcReaches a b :=
  .tail (.refl a) e

theorem reach_closed (a : RfcState) : RfcReaches a .closed :=
  .single (.close a)

theorem reach_start_waitFinished : RfcReaches .start .waitFinished :=
  (((RfcReaches.single .recvClientHello).tail .selectParameters).tail
    .sendFlight).tail .flight2Complete

theorem reach_start_connected : RfcReaches .start .connected :=
  reach_start_waitFinished.tail .recvFinished

theorem reach_waitFinished_connected : RfcReaches .waitFinished .connected :=
  .single .recvFinished

/-! ## The refinement: implementation ⊑ RFC spec -/

/-- The abstraction: which RFC state each implementation phase represents.

The opaque handshake engine (`Config.hsFeed`) collapses RECVD_CH ..
WAIT_FINISHED into two implementation phases, so `accum` reads as START
(no complete ClientHello yet) and `handshaking` reads as WAIT_FINISHED
(the furthest pre-CONNECTED handshake state — the one whose single RFC
edge to CONNECTED is `Recv Finished`). Every established phase reads as
CONNECTED (the record layer is live, in userspace or offloaded to the
kernel). `closing`/`closed` read as CONNECTED-teardown, i.e. `closed`. -/
def absPhase : Phase → RfcState
  | .accum _ _ => .start
  | .handshaking _ _ => .waitFinished
  | .estabUser _ _ _ => .connected
  | .offloadAttach _ _ _ _ => .connected
  | .installingTx _ _ _ => .connected
  | .installingRx _ _ => .connected
  | .estabOffload _ => .connected
  | .closing => .closed
  | .closed => .closed

/-- Application-data outputs: full record-layer plaintext in either
direction. `deliverEarly` (0.5-RTT early data) is deliberately **not**
here — it is the RFC's separately-gated 0-RTT exception (RFC 8446 §2.3,
§4.2.10), handled by `Tls.early_data_needs_flag`. -/
def isAppData : Output → Bool
  | .sendPlain _ => true
  | .deliverPlain _ => true
  | _ => false

/-- No output of the list carries application data. -/
def noApp (l : List Output) : Prop := ∀ o ∈ l, isAppData o = false

theorem noApp_nil : noApp [] := by intro _ h; cases h

theorem noApp_append {l₁ l₂ : List Output}
    (h₁ : noApp l₁) (h₂ : noApp l₂) : noApp (l₁ ++ l₂) := by
  intro o h
  rcases List.mem_append.1 h with h | h
  · exact h₁ o h
  · exact h₂ o h

theorem noApp_sendIf (b : Bytes) : noApp (sendIf b) := by
  intro o h; rw [mem_sendIf h]; rfl

theorem noApp_earlyIf (cfg : Config) (b : Bytes) : noApp (earlyIf cfg b) := by
  intro o h; rw [(mem_earlyIf h).2]; rfl

theorem noApp_singleton_send (b : Bytes) : noApp [Output.send b] := by
  intro o h; simp at h; subst h; rfl

theorem noApp_singleton_close : noApp [Output.close] := by
  intro o h; simp at h; subst h; rfl

theorem noApp_fatal (b : Bytes) : noApp [Output.send b, Output.close] := by
  intro o h; simp at h; rcases h with h | h <;> subst h <;> rfl

theorem noApp_attach (snd early : Bytes) (cfg : Config) :
    noApp (sendIf snd ++ earlyIf cfg early ++ [Output.attachUlp]) := by
  refine noApp_append (noApp_append (noApp_sendIf snd) (noApp_earlyIf cfg early)) ?_
  intro o h; simp at h; subst h; rfl

/-- `finishHs` never emits application data: both policy branches emit
only wire records, early data, and (under `ktls`) the `attachUlp` request. -/
theorem finishHs_noApp (cfg : Config) (alpn : Alpn) (rc : RecConn)
    (rest snd early : Bytes) : noApp (finishHs cfg alpn rc rest snd early).2.out := by
  unfold finishHs
  split
  · exact noApp_attach snd early cfg
  · exact noApp_append (noApp_sendIf snd) (noApp_earlyIf cfg early)

/-- `hsDrive` never emits application data: every branch (insufficient,
more, done via `finishHs`, fail) emits only wire records / early data /
`close`. -/
theorem hsDrive_noApp (cfg : Config) (hs : HsConn) (buf : Bytes)
    (stay : HsConn → Bytes → Phase) : noApp (hsDrive cfg hs buf stay).2.out := by
  unfold hsDrive
  split <;>
    first
    | exact noApp_nil
    | exact noApp_append (noApp_sendIf _) (noApp_earlyIf _ _)
    | exact finishHs_noApp _ _ _ _ _ _
    | exact noApp_fatal _

/-- **No application data before CONNECTED.** From any phase whose
abstraction is not CONNECTED (`accum`, `handshaking`, `closing`, `closed`),
a step emits no `sendPlain`/`deliverPlain`. In particular the client can
send no application data that reaches the application before the handshake
completes (its Finished is verified). -/
theorem no_appdata_before_connected (cfg : Config) (s : St) (i : Input)
    (h : absPhase s.phase ≠ .connected) :
    ∀ o ∈ (step cfg s i).2.out, isAppData o = false := by
  have hgoal : noApp (stepPhase cfg s.phase i).2.out →
      ∀ o ∈ (step cfg s i).2.out, isAppData o = false := by
    intro hn o ho; exact hn o ho
  apply hgoal
  rcases s with ⟨p, g⟩
  simp only [absPhase] at h
  cases p with
  | accum hs buf =>
    cases i with
    | bytesReceived d => exact hsDrive_noApp cfg hs (buf ++ d) .accum
    | closeRequested => exact noApp_singleton_close
    | peerClosed => exact noApp_singleton_close
    | appData d => exact noApp_nil
    | ulpAttached => exact noApp_nil
    | ulpUnavailable => exact noApp_nil
    | installOk => exact noApp_nil
    | installFailed => exact noApp_nil
    | sendDrained => exact noApp_nil
  | handshaking hs buf =>
    cases i with
    | bytesReceived d => exact hsDrive_noApp cfg hs (buf ++ d) .handshaking
    | closeRequested => exact noApp_singleton_close
    | peerClosed => exact noApp_singleton_close
    | appData d => exact noApp_nil
    | ulpAttached => exact noApp_nil
    | ulpUnavailable => exact noApp_nil
    | installOk => exact noApp_nil
    | installFailed => exact noApp_nil
    | sendDrained => exact noApp_nil
  | estabUser => exact absurd rfl h
  | offloadAttach => exact absurd rfl h
  | installingTx => exact absurd rfl h
  | installingRx => exact absurd rfl h
  | estabOffload => exact absurd rfl h
  | closing =>
    cases i <;> first | exact noApp_singleton_close | exact noApp_nil
  | closed =>
    cases i <;> exact noApp_nil

/-- Predicate: the handshake engine reports completion (Finished). -/
def HsOut.isDone : HsOut → Prop
  | .done _ _ _ _ _ => True
  | _ => False

/-- **CONNECTED is entered only on a completing handshake.** If a step
moves the abstract state to CONNECTED from a non-CONNECTED phase, then the
phase was `accum`/`handshaking`, the input was `bytesReceived d`, and the
handshake engine reported `.done` on the accumulated ciphertext — the
concrete realization of the RFC "Recv Finished" edge. No other input can
reach CONNECTED. -/
theorem connected_only_via_hsDone (cfg : Config) (s : St) (i : Input)
    (hpre : absPhase s.phase ≠ .connected)
    (hpost : absPhase (step cfg s i).1.phase = .connected) :
    ∃ hs buf d, (s.phase = .accum hs buf ∨ s.phase = .handshaking hs buf)
      ∧ i = .bytesReceived d ∧ HsOut.isDone (cfg.hsFeed hs (buf ++ d)) := by
  rcases s with ⟨p, g⟩
  simp only [absPhase] at hpre
  -- The post-state phase of a `step` is the `stepPhase` phase.
  have hstep : (step cfg ⟨p, g⟩ i).1.phase = (stepPhase cfg p i).1 := rfl
  rw [hstep] at hpost
  cases p with
  | accum hs buf =>
    cases i with
    | bytesReceived d =>
      refine ⟨hs, buf, d, Or.inl rfl, rfl, ?_⟩
      -- absPhase of hsDrive's result is connected only in the `.done` branch.
      simp only [stepPhase, hsDrive] at hpost
      cases hfeed : cfg.hsFeed hs (buf ++ d) with
      | insufficient => rw [hfeed] at hpost; simp [absPhase] at hpost
      | more hs' n snd early => rw [hfeed] at hpost; simp [absPhase] at hpost
      | done rc n snd alpn early => trivial
      | fail => rw [hfeed] at hpost; simp [absPhase] at hpost
    | closeRequested => simp [stepPhase, absPhase] at hpost
    | peerClosed => simp [stepPhase, absPhase] at hpost
    | appData d => simp [stepPhase, absPhase] at hpost
    | ulpAttached => simp [stepPhase, absPhase] at hpost
    | ulpUnavailable => simp [stepPhase, absPhase] at hpost
    | installOk => simp [stepPhase, absPhase] at hpost
    | installFailed => simp [stepPhase, absPhase] at hpost
    | sendDrained => simp [stepPhase, absPhase] at hpost
  | handshaking hs buf =>
    cases i with
    | bytesReceived d =>
      refine ⟨hs, buf, d, Or.inr rfl, rfl, ?_⟩
      simp only [stepPhase, hsDrive] at hpost
      cases hfeed : cfg.hsFeed hs (buf ++ d) with
      | insufficient => rw [hfeed] at hpost; simp [absPhase] at hpost
      | more hs' n snd early => rw [hfeed] at hpost; simp [absPhase] at hpost
      | done rc n snd alpn early => trivial
      | fail => rw [hfeed] at hpost; simp [absPhase] at hpost
    | closeRequested => simp [stepPhase, absPhase] at hpost
    | peerClosed => simp [stepPhase, absPhase] at hpost
    | appData d => simp [stepPhase, absPhase] at hpost
    | ulpAttached => simp [stepPhase, absPhase] at hpost
    | ulpUnavailable => simp [stepPhase, absPhase] at hpost
    | installOk => simp [stepPhase, absPhase] at hpost
    | installFailed => simp [stepPhase, absPhase] at hpost
    | sendDrained => simp [stepPhase, absPhase] at hpost
  | estabUser => exact absurd rfl hpre
  | offloadAttach => exact absurd rfl hpre
  | installingTx => exact absurd rfl hpre
  | installingRx => exact absurd rfl hpre
  | estabOffload => exact absurd rfl hpre
  | closing => cases i <;> simp [stepPhase, absPhase] at hpost
  | closed => cases i <;> simp [stepPhase, absPhase] at hpost

/-- **Transition agreement.** Every implementation step moves the abstract
state along an RFC-permitted path. -/
theorem transition_agreement (cfg : Config) (s : St) (i : Input) :
    RfcReaches (absPhase s.phase) (absPhase (step cfg s i).1.phase) := by
  have hstep : (step cfg s i).1.phase = (stepPhase cfg s.phase i).1 := rfl
  rw [hstep]
  rcases s with ⟨p, g⟩
  cases p with
  | accum hs buf =>
    cases i with
    | bytesReceived d =>
      simp only [stepPhase, hsDrive]
      split <;>
        first
        | (simp only [absPhase]; exact .refl _)
        | (simp only [absPhase]; exact reach_start_waitFinished)
        | (simp only [finishHs]; split <;> (simp only [absPhase]; exact reach_start_connected))
        | (simp only [absPhase]; exact reach_closed _)
    | closeRequested => simp only [stepPhase, absPhase]; exact reach_closed _
    | peerClosed => simp only [stepPhase, absPhase]; exact reach_closed _
    | appData d => simp only [stepPhase, absPhase]; exact .refl _
    | ulpAttached => simp only [stepPhase, absPhase]; exact .refl _
    | ulpUnavailable => simp only [stepPhase, absPhase]; exact .refl _
    | installOk => simp only [stepPhase, absPhase]; exact .refl _
    | installFailed => simp only [stepPhase, absPhase]; exact .refl _
    | sendDrained => simp only [stepPhase, absPhase]; exact .refl _
  | handshaking hs buf =>
    cases i with
    | bytesReceived d =>
      simp only [stepPhase, hsDrive]
      split <;>
        first
        | (simp only [absPhase]; exact .refl _)
        | (simp only [finishHs]; split <;> (simp only [absPhase]; exact reach_waitFinished_connected))
        | (simp only [absPhase]; exact reach_closed _)
    | closeRequested => simp only [stepPhase, absPhase]; exact reach_closed _
    | peerClosed => simp only [stepPhase, absPhase]; exact reach_closed _
    | appData d => simp only [stepPhase, absPhase]; exact .refl _
    | ulpAttached => simp only [stepPhase, absPhase]; exact .refl _
    | ulpUnavailable => simp only [stepPhase, absPhase]; exact .refl _
    | installOk => simp only [stepPhase, absPhase]; exact .refl _
    | installFailed => simp only [stepPhase, absPhase]; exact .refl _
    | sendDrained => simp only [stepPhase, absPhase]; exact .refl _
  | estabUser alpn rc buf =>
    cases i with
    | bytesReceived d =>
      simp only [stepPhase, recDrive]
      split <;>
        first
        | (simp only [absPhase]; exact .refl _)
        | (simp only [absPhase]; exact reach_closed _)
    | closeRequested => simp only [stepPhase, absPhase]; exact reach_closed _
    | peerClosed => simp only [stepPhase, absPhase]; exact reach_closed _
    | appData d => simp only [stepPhase, absPhase]; exact .refl _
    | ulpAttached => simp only [stepPhase, absPhase]; exact .refl _
    | ulpUnavailable => simp only [stepPhase, absPhase]; exact .refl _
    | installOk => simp only [stepPhase, absPhase]; exact .refl _
    | installFailed => simp only [stepPhase, absPhase]; exact .refl _
    | sendDrained => simp only [stepPhase, absPhase]; exact .refl _
  | offloadAttach alpn rc buf pend =>
    cases i with
    | ulpAttached => simp only [stepPhase, absPhase]; exact .refl _
    | ulpUnavailable => simp only [stepPhase, absPhase]; exact .refl _
    | installFailed => simp only [stepPhase, absPhase]; exact reach_closed _
    | bytesReceived d => simp only [stepPhase, absPhase]; exact .refl _
    | appData d => simp only [stepPhase, absPhase]; exact .refl _
    | closeRequested => simp only [stepPhase, absPhase]; exact reach_closed _
    | peerClosed => simp only [stepPhase, absPhase]; exact reach_closed _
    | installOk => simp only [stepPhase, absPhase]; exact .refl _
    | sendDrained => simp only [stepPhase, absPhase]; exact .refl _
  | installingTx alpn rx pend =>
    cases i with
    | installOk => simp only [stepPhase, absPhase]; exact .refl _
    | installFailed => simp only [stepPhase, absPhase]; exact reach_closed _
    | appData d => simp only [stepPhase, absPhase]; exact .refl _
    | closeRequested => simp only [stepPhase, absPhase]; exact reach_closed _
    | peerClosed => simp only [stepPhase, absPhase]; exact reach_closed _
    | bytesReceived d => simp only [stepPhase, absPhase]; exact .refl _
    | ulpAttached => simp only [stepPhase, absPhase]; exact .refl _
    | ulpUnavailable => simp only [stepPhase, absPhase]; exact .refl _
    | sendDrained => simp only [stepPhase, absPhase]; exact .refl _
  | installingRx alpn pend =>
    cases i with
    | installOk => simp only [stepPhase, absPhase]; exact .refl _
    | installFailed => simp only [stepPhase, absPhase]; exact reach_closed _
    | appData d => simp only [stepPhase, absPhase]; exact .refl _
    | closeRequested => simp only [stepPhase, absPhase]; exact reach_closed _
    | peerClosed => simp only [stepPhase, absPhase]; exact reach_closed _
    | bytesReceived d => simp only [stepPhase, absPhase]; exact .refl _
    | ulpAttached => simp only [stepPhase, absPhase]; exact .refl _
    | ulpUnavailable => simp only [stepPhase, absPhase]; exact .refl _
    | sendDrained => simp only [stepPhase, absPhase]; exact .refl _
  | estabOffload alpn =>
    cases i with
    | bytesReceived d => simp only [stepPhase, absPhase]; exact .refl _
    | appData d => simp only [stepPhase, absPhase]; exact .refl _
    | closeRequested => simp only [stepPhase, absPhase]; exact reach_closed _
    | peerClosed => simp only [stepPhase, absPhase]; exact reach_closed _
    | ulpAttached => simp only [stepPhase, absPhase]; exact .refl _
    | ulpUnavailable => simp only [stepPhase, absPhase]; exact .refl _
    | installOk => simp only [stepPhase, absPhase]; exact .refl _
    | installFailed => simp only [stepPhase, absPhase]; exact .refl _
    | sendDrained => simp only [stepPhase, absPhase]; exact .refl _
  | closing =>
    cases i with
    | sendDrained => simp only [stepPhase, absPhase]; exact .refl _
    | peerClosed => simp only [stepPhase, absPhase]; exact .refl _
    | bytesReceived d => simp only [stepPhase, absPhase]; exact .refl _
    | appData d => simp only [stepPhase, absPhase]; exact .refl _
    | closeRequested => simp only [stepPhase, absPhase]; exact .refl _
    | ulpAttached => simp only [stepPhase, absPhase]; exact .refl _
    | ulpUnavailable => simp only [stepPhase, absPhase]; exact .refl _
    | installOk => simp only [stepPhase, absPhase]; exact .refl _
    | installFailed => simp only [stepPhase, absPhase]; exact .refl _
  | closed =>
    cases i <;> (simp only [stepPhase, absPhase]; exact .refl _)

/-- Corollary over the reachability predicate: the abstract state of any
reachable implementation state is RFC-reachable from START (the abstract
initial state), and remains inside the RFC diagram. -/
theorem reachable_abs_from_start (cfg : Config) (s : St)
    (h : Reachable cfg s) : RfcReaches .start (absPhase s.phase) := by
  induction h with
  | init => simp only [init, absPhase]; exact .refl _
  | step hs i ih =>
    -- one more implementation step: chain the path with transition_agreement.
    rename_i s'
    have hstep := transition_agreement cfg s' i
    exact rfcReaches_trans ih hstep
where
  rfcReaches_trans {a b c : RfcState}
      (h₁ : RfcReaches a b) (h₂ : RfcReaches b c) : RfcReaches a c := by
    induction h₂ with
    | refl => exact h₁
    | tail _ e ih => exact .tail ih e

end TlsRfc
