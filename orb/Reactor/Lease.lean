import Reactor.Contract
import Reactor.Deploy
import Uring.Lts
import Uring.RecycleOnce

/-!
# A-compose — the reactor recycle, composed against the ring LTS

`Reactor.Contract` proves recycle-exactly-once *at the reactor level*: a
`recvInto bid` event yields exactly one `recycleBuffer bid` submission and no
other event yields any (`recv_recycles_exactly_once`, `non_recv_no_recycle`).
That statement is about the reactor's output list in isolation — it does not yet
say the recycled `bid` is a buffer the ring actually lent the client.

This file closes that gap at the single-step level and bridges to the ring's own
trace-level guarantee (`Uring.recycle_at_most_once`).

## The coupling

A `recvInto bid data` event does not arise from nowhere: the copy-once reactor
only ever sees a recv completion because the client *reaped* a buffer-select
completion carrying `bid`, which (by `Uring.dispatch`) placed `bid` into
`held`. We name that fact `Leased bid s := bid ∈ s.held` and show it is exactly
what a reap of a `.buf bid` completion establishes (`reap_establishes_lease`).

## What is proven (zero sorries)

* `reap_establishes_lease` — the coupling constructor: reaping a buffer-select
  completion for `bid` puts `bid ∈ held`.
* `reactor_recycle_is_held` — **the A-compose single step**: when the reactor
  emits `recycleBuffer bid` in response to `recvInto bid` *and* the coupling
  holds (`bid ∈ held`), the ring's `Uring.Step.recycle bid` is enabled. The
  reactor only ever asks to recycle a buffer the ring lent it.
* `recv_recycle_labels` — the reactor's recv step, read as ring labels, is
  exactly `[Uring.Lbl.recycle bid]`: the copy-once obligation contributes one
  recycle label, the translated FSM outputs contribute none.
* `reactor_recycle_trace` — that single recycle label is a one-step ring
  `Trace` from the leased state.
* `reactor_recycle_at_most_once` — the ring's `recycle_at_most_once`, transported
  to reactor-emitted recycle labels: across any ring trace from init, two
  recycles of the same `bid` are separated by a fresh delivery of `bid`.

## What is UNCLOSED (honest)

The *full* reactor+LTS product induction — that an arbitrary stream of reactor
events, interleaved with the demonic environment's reaps/deliveries/exhaustion,
assembles into a single valid `Uring.Trace` whose recycle labels are precisely
the reactor's emitted ones — is **not** built here. `reactor_recycle_trace`
supplies the one-step embedding and `reactor_recycle_at_most_once` supplies the
trace-level no-double-recycle; the missing piece is the interleaving driver that
threads reactor steps and environment steps into one product trace. See
`Reactor/LEASE-README.md`.
-/

namespace Reactor

open Proto (Bytes)

/-- **The coupling.** A reactor `recvInto bid` event is justified by the ring
having just leased `bid` to the client: the ring state has `bid ∈ held`. -/
def Leased (bid : Uring.Bid) (s : Uring.St) : Prop := bid ∈ s.held

/-- **Coupling constructor.** Reaping a buffer-select completion carrying `bid`
(the `.buf bid` payload) establishes the lease: the post-reap ring state holds
`bid`. This is the `Uring` side of a reactor `recvInto bid` event. -/
theorem reap_establishes_lease {s : Uring.St} {c : Uring.Cqe}
    {rest : List Uring.Cqe} {bid : Uring.Bid}
    (hpay : c.payload = Uring.Payload.buf bid) :
    Leased bid (Uring.dispatch { s with cq := rest } c) := by
  simp [Leased, Uring.dispatch, hpay]

/-- The same fact stated against an actual `Uring.Step.reap` transition: after
reaping a completion whose payload is `.buf bid`, the ring holds `bid`. -/
theorem step_reap_establishes_lease {cfg : Uring.Cfg} {s s' : Uring.St}
    {c : Uring.Cqe} {rest : List Uring.Cqe} {bid : Uring.Bid}
    (hstep : Uring.Step cfg s (.reap c) s')
    (hcq : s.cq = c :: rest) (hpay : c.payload = Uring.Payload.buf bid) :
    Leased bid s' := by
  cases hstep with
  | reap hcq' =>
      -- the queue head is unique, so `rest` here is the reaped tail
      rw [hcq] at hcq'
      cases hcq'
      exact reap_establishes_lease hpay

/-- The reactor's recv step emits the recycle of exactly that buffer (membership
form of `recv_recycles_exactly_once`). -/
theorem recv_emits_recycle (cfg : Proto.Config) (s : Proto.State)
    (bid : Uring.Bid) (data : Bytes) :
    RingSubmission.recycleBuffer bid ∈ (step cfg s (.recvInto bid data)).2 := by
  simp [step]

/-- **A-compose, single step.** When the reactor emits `recycleBuffer bid` in
response to `recvInto bid` and the coupling holds (`bid` is one the ring lent —
`bid ∈ held`), the ring's `recycle bid` move is enabled. The reactor only ever
asks to recycle a buffer the ring actually leased it. -/
theorem reactor_recycle_is_held
    (cfg : Proto.Config) (st : Proto.State) (bid : Uring.Bid) (data : Bytes)
    (ucfg : Uring.Cfg) (us : Uring.St) (hlease : Leased bid us) :
    RingSubmission.recycleBuffer bid ∈ (step cfg st (.recvInto bid data)).2
      ∧ ∃ us', Uring.Step ucfg us (.recycle bid) us' :=
  ⟨recv_emits_recycle cfg st bid data,
   Uring.recycle_enabled (cfg := ucfg) (s := us) (b := bid) hlease⟩

/-! ## Label-level bridge to the ring's trace guarantee -/

/-- The `Uring` recycle labels a reactor submission list requests. -/
def recycleLabels : List RingSubmission → List Uring.Lbl
  | [] => []
  | .recycleBuffer b :: rest => Uring.Lbl.recycle b :: recycleLabels rest
  | _ :: rest => recycleLabels rest

@[simp] theorem recycleLabels_nil : recycleLabels [] = [] := rfl

theorem recycleLabels_append (l₁ l₂ : List RingSubmission) :
    recycleLabels (l₁ ++ l₂) = recycleLabels l₁ ++ recycleLabels l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l ih => cases a <;> simp [recycleLabels, ih]

/-- A submission list with no recycle (the `isRecycle` filter is empty) yields
no recycle labels. -/
theorem recycleLabels_of_no_recycle (l : List RingSubmission)
    (h : l.filter RingSubmission.isRecycle = []) : recycleLabels l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases a <;>
        simp only [List.filter_cons, RingSubmission.isRecycle, if_true,
          if_false] at h ⊢ <;>
        first
        | exact absurd h (List.cons_ne_nil _ _)
        | simp [recycleLabels, ih h]

/-- **The recv step, read as ring labels, is exactly one recycle.** The
translated FSM outputs contribute no recycle labels (`map_ofOutput_no_recycle`);
the copy-once obligation contributes exactly `recycle bid`. -/
theorem recv_recycle_labels (cfg : Proto.Config) (s : Proto.State)
    (bid : Uring.Bid) (data : Bytes) :
    recycleLabels (step cfg s (.recvInto bid data)).2
      = [Uring.Lbl.recycle bid] := by
  simp only [step, recycleLabels_append,
    recycleLabels_of_no_recycle _ (map_ofOutput_no_recycle _)]
  rfl

/-- **The emitted recycle label is a one-step ring trace** from the leased
state: the reactor's request extends any ring trace by a valid `recycle` move. -/
theorem reactor_recycle_trace {ucfg : Uring.Cfg} {us : Uring.St}
    {bid : Uring.Bid} (hlease : Leased bid us) :
    ∃ us', Uring.Trace ucfg us [Uring.Lbl.recycle bid] us' := by
  obtain ⟨us', h⟩ := Uring.recycle_enabled (cfg := ucfg) (s := us) (b := bid) hlease
  exact ⟨us', Uring.Trace.single h⟩

/-- **A-compose, trace level (the ring's guarantee, transported).** Across any
ring trace from the initial state, two recycles of the same `bid` are separated
by a fresh delivery of `bid`. Since the reactor's recycle requests are `recycle`
labels (`recv_recycle_labels`) and each is an enabled ring move
(`reactor_recycle_trace`), a reactor-driven trace inherits no-double-recycle:
each lent `bid` is recycled at most once. This is `Uring.recycle_at_most_once`
at the reactor's emitted labels. -/
theorem reactor_recycle_at_most_once {cfg : Uring.Cfg} {sfin : Uring.St}
    {b : Uring.Bid} {m₁ m₂ m₃ : List Uring.Lbl}
    (tr : Uring.Trace cfg (Uring.init cfg)
      (m₁ ++ .recycle b :: (m₂ ++ .recycle b :: m₃)) sfin) :
    ∃ fd more, Uring.Lbl.deliver fd b more ∈ m₂ :=
  Uring.recycle_at_most_once tr

/-! ## The deployed path

`reactor_recycle_is_held` is generic over the `Proto.Config`. The deployed orb
runs the reactor over `Reactor.Deploy.deployConfig`, and its recv event carries
buffer id `0` (`deploySubs input` is definitionally `(Reactor.step deployConfig
(active mkPlain) (recvInto 0 input)).2`). Instantiating the coupling at that
config lands it on exactly the submission list `main` acts on. -/

/-- **`reactor_recycle_is_held_deployed` — the DEPLOYED reactor only recycles a
buffer the ring lent it.** On the deployed submission list `deploySubs input`, the
copy-once obligation emits `recycleBuffer 0`, and whenever the coupling holds
(`0 ∈ held` — the ring leased buffer `0` to the client), the ring's `recycle 0`
move is enabled. `reactor_recycle_is_held` instantiated at `deployConfig` and the
fresh plain connection, so the membership fact is about `Reactor.Deploy.deploySubs
input` itself. -/
theorem reactor_recycle_is_held_deployed
    (input : Bytes) (ucfg : Uring.Cfg) (us : Uring.St)
    (hlease : Leased 0 us) :
    RingSubmission.recycleBuffer 0 ∈ Reactor.Deploy.deploySubs input
      ∧ ∃ us', Uring.Step ucfg us (.recycle 0) us' :=
  reactor_recycle_is_held Reactor.Deploy.deployConfig
    (.active Proto.Conn.mkPlain) 0 input ucfg us hlease

end Reactor
