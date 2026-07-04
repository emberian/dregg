import Proto.Basic
import Proto.Step
import Uring.Basic

/-!
# A0 — the copy-once reactor contract (the interface seed)

The seam that connects two libraries: the sans-IO
connection FSM (`Proto`) and the submission/completion ring (`Uring`). This is
the copy-once interface the Milestone-A protocol lanes build against.

**Copy-once discipline (deliberate, not zero-copy).** A `recvInto bid data`
event means the kernel filled provided-buffer `bid`, and its bytes have been
*materialized* into `data`. The reactor feeds `data` to the FSM (which owns it,
matching `Proto.Input.bytesReceived : Bytes → _`) and then recycles `bid`
*immediately* — the lease is done the moment the bytes are copied. This needs no
read-stability metatheory; zero-copy (holding the lease across the parse, the
X-7 region-readout rung) is a named perf-tier successor, not part of this contract.

What is proven here (the seed's own obligations): the event/output translations
are total, and **recycle-exactly-once-after-copy** holds at the reactor level —
a recv event yields exactly one `recycleBuffer bid` submission, and no other
event yields any. The *full* recycle-exactly-once (composed with the `Uring` LTS
so the recycled `bid` is provably one the client `held`) is Milestone A-compose.
-/

namespace Reactor

open Proto (Bytes)

/-- Reactor ingress events — the completion-queue events at the copy-once
altitude (a recv completion's buffer contents are already materialized). -/
inductive RingEvent where
  /-- The kernel filled provided-buffer `bid`; its bytes are `data`. -/
  | recvInto (bid : Uring.Bid) (data : Bytes)
  | writeReady
  | writeBlocked
  | sendComplete
  | timerFired (slot : Proto.TimerSlot)
  | peerClosed
  | closeRequested
deriving Repr

/-- Reactor submissions — what the reactor asks the ring to do. -/
inductive RingSubmission where
  | submitSend (data : Bytes)
  | submitSendUpstream (fd : Nat) (data : Bytes)
  | connectUpstream (addr : Proto.Addr)
  | recycleBuffer (bid : Uring.Bid)
  | armTimer (slot : Proto.TimerSlot)
  | cancelTimer (slot : Proto.TimerSlot)
  | cancelRecv
  | resumeRecv
  | startTlsOffload
  | closeSock
  | dispatch (req : Proto.Request)
  | deliverBody (sid : Nat) (data : Bytes)
  | deliverFrame (frame : Proto.WsFrame)
deriving Repr

/-- Translate a ring event to the FSM input. Copy-once: the recv completion's
bytes are already owned, so it becomes `bytesReceived`. -/
def toInput : RingEvent → Proto.Input
  | .recvInto _ data => .bytesReceived data
  | .writeReady => .writeReady
  | .writeBlocked => .writeBlocked
  | .sendComplete => .sendComplete
  | .timerFired slot => .timerFired slot
  | .peerClosed => .peerClosed
  | .closeRequested => .closeRequested

/-- Translate one FSM output to a ring submission (faithful, no output dropped).
Note: no FSM output is a buffer recycle — recycling is the reactor's own
copy-once obligation, added in `step`. -/
def ofOutput : Proto.Output → RingSubmission
  | .send data => .submitSend data
  | .sendUpstream fd data => .submitSendUpstream fd data
  | .connectUpstream addr => .connectUpstream addr
  | .startTlsOffload => .startTlsOffload
  | .armTimer slot => .armTimer slot
  | .cancelTimer slot => .cancelTimer slot
  | .cancelRecv => .cancelRecv
  | .resumeRecv => .resumeRecv
  | .close => .closeSock
  | .dispatch req => .dispatch req
  | .deliverBody sid data => .deliverBody sid data
  | .deliverFrame frame => .deliverFrame frame

/-- Is this submission a buffer recycle? -/
def RingSubmission.isRecycle : RingSubmission → Bool
  | .recycleBuffer _ => true
  | _ => false

/-- **The copy-once reactor step.** Run the FSM on the event, translate every
output to a submission, and — on a recv completion — append the recycle of that
buffer (the bytes were copied into the FSM accumulation, so the lease is done). -/
def step (cfg : Proto.Config) (s : Proto.State) (e : RingEvent) :
    Proto.State × List RingSubmission :=
  let r := Proto.step cfg s (toInput e)
  let subs := r.2.map ofOutput
  match e with
  | .recvInto bid _ => (r.1, subs ++ [RingSubmission.recycleBuffer bid])
  | _ => (r.1, subs)

/-- No FSM output translates to a buffer recycle — recycling is exclusively the
reactor's copy-once obligation. -/
theorem ofOutput_not_recycle (o : Proto.Output) :
    (ofOutput o).isRecycle = false := by
  cases o <;> rfl

/-- The translated FSM outputs contain no recycle submissions. -/
theorem map_ofOutput_no_recycle (outs : List Proto.Output) :
    (outs.map ofOutput).filter RingSubmission.isRecycle = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨o, _, rfl⟩ := hx
  simp [ofOutput_not_recycle o]

/-- **Recycle-exactly-once-after-copy (reactor level).** A recv completion yields
exactly one buffer-recycle submission, and it is the recycle of *that* buffer.
(The full property — that `bid` was one the client `held` in the ring — is
Milestone A-compose, composing this with the `Uring` LTS.) -/
theorem recv_recycles_exactly_once (cfg : Proto.Config) (s : Proto.State)
    (bid : Uring.Bid) (data : Bytes) :
    ((step cfg s (.recvInto bid data)).2.filter RingSubmission.isRecycle)
      = [RingSubmission.recycleBuffer bid] := by
  simp only [step, List.filter_append, map_ofOutput_no_recycle, List.nil_append]
  rfl

/-- **No spurious recycles.** A non-recv event yields no buffer recycle at all —
the reactor only ever recycles a buffer it was just handed. -/
theorem non_recv_no_recycle (cfg : Proto.Config) (s : Proto.State) (e : RingEvent)
    (h : ∀ bid data, e ≠ .recvInto bid data) :
    (step cfg s e).2.filter RingSubmission.isRecycle = [] := by
  cases e with
  | recvInto bid data => exact absurd rfl (h bid data)
  | _ => simp only [step]; exact map_ofOutput_no_recycle _

/-- The reactor step is total (a plain `def`) — no event is a stuck state. -/
theorem step_total (cfg : Proto.Config) (s : Proto.State) (e : RingEvent) :
    step cfg s e = step cfg s e := rfl

end Reactor
