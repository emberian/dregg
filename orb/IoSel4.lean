/-
IoSel4 — the seL4 Microkit / sDDF IO boundary for the net protection domain.

This is a SKELETON. It does not run here: a real target needs the Microkit SDK,
the sDDF net driver, and a CapDL init image (see `SEL4-IO-README.md`). What this
file provides is the *typed seam* between the proven reactor core and the seL4
substrate, so that the boundary is small, every crossing is named `TRUSTED`, and
the Lean-side buffer-lease invariants are stated relative to it.

Two families of declarations live here:

  * IMPORTS (`@[extern]`, TRUSTED foreign code): the sDDF net-queue ops and the
    Microkit protection-domain primitives the net PD calls. No Lean body — the
    implementation is C in the seL4 image; these are opaque at the boundary.
  * EXPORTS (`@[export]`, the Microkit entry points): `init` / `notified` /
    `protected`, the symbols libmicrokit's crt0 calls back into. Their bodies are
    the untrusted-but-tested IO shell; the one line that matters — the crossing
    onto the proven core — is `Reactor.Ingress.deployStepIngress`, called from the
    pure `serviceOne` below, exactly as `Arena.Orb.main` calls it over stdin.

The proven core is sacred and is not modified: the shell dequeues a filled RX
buffer, hands its bytes to `deployStepIngress`, and enqueues the response bytes on
TX. The socket/accept loop of the Linux driver is replaced by the sDDF ring
dequeue/enqueue; the reactor step in the middle is byte-for-byte the same.

The second half of the file is the REFINEMENT MAPPING: the sDDF shared-ring is a
strictly-smaller LTS than the `Uring` submission/completion ring already proven in
this repo. We give the abstraction function `toUringSt` from an sDDF RX ring
occupancy to a `Uring.St`, prove it is faithful on the bid multiset
(`owned_toUringSt`), and STATE (do not discharge here) the step-embedding
obligation whose discharge transports `Uring.conservation` / `Uring.no_leak` /
`Uring.recycle_at_most_once` onto the sDDF path. That obligation is the real seL4
slice's work; here it is only machine-checked to be a well-formed statement.
-/
import Reactor.Ingress
import Reactor.Observe
import Uring.Basic
import Uring.Conservation
import Uring.RecycleOnce

namespace IoSel4

open Proto (Bytes)

/-! ## sDDF descriptor ring — the shared types

The sDDF net transport is four single-producer/single-consumer rings across the
driver↔client (net PD) shared-memory region, two per direction:

  * RX free   — client → driver: empty buffers lent to the NIC to fill.
  * RX active — driver → client: filled buffers (a received packet).
  * TX active — client → driver: filled buffers to transmit.
  * TX free   — driver → client: buffers whose transmission has completed.

Each ring is a fixed-capacity array of `BuffDesc` with a producer `tail` and a
consumer `head` index (`net_queue_t` in the C library). A descriptor names an
offset into the shared DMA data region and a byte length — it does NOT carry the
bytes; the bytes live in the data region the CapDL image maps into both PDs. -/

/-- An sDDF buffer descriptor: `net_buff_desc_t`. `ioOrOffset` is a byte offset
into the shared data region (an IO address on the driver side); `len` is the
filled length. -/
structure BuffDesc where
  ioOrOffset : UInt64
  len        : UInt16
deriving Repr, DecidableEq, Inhabited

/-- A single sDDF SPSC ring: a capacity, a producer tail, a consumer head, and
the descriptor slots. Concretely `net_queue_t` sharing one page across the PD
boundary. The head/tail indices are the only mutable state the two PDs jointly
observe; every crossing of them is an seL4 shared-memory access ordered by the
Microkit notification discipline. -/
structure Ring where
  capacity : Nat
  head     : Nat
  tail     : Nat
  slots    : Array BuffDesc
deriving Repr, Inhabited

/-- One direction's pair of rings (free + active), i.e. an `net_queue_handle_t`. -/
structure QueueHandle where
  free   : Ring
  active : Ring
deriving Repr, Inhabited

/-- The net PD's full ring context: RX and TX handles, plus the base of the
shared data region the descriptors offset into. -/
structure NetCtx where
  rx       : QueueHandle
  tx       : QueueHandle
  dataBase : UInt64
deriving Repr, Inhabited

/-! ## Microkit protection-domain primitives (TRUSTED imports)

Microkit gives a PD two ways to be entered and two ways to act: an asynchronous
`notified(channel)` when a peer signals a badged notification, and a synchronous
`protected(channel, msginfo)` when a peer does a protected procedure call
(`seL4_Call`). To act, the PD signals a channel (`microkit_notify`) or defers the
signal to its next return-to-kernel (`microkit_deferred_notify`), and acks IRQs
(`microkit_irq_ack`). These are the seL4 IPC surface; there is no other authority
in a NIC-cap-only confined PD. -/

/-- Microkit channel id (a badge / capability slot into the PD's cspace). -/
abbrev Channel := UInt32

/-- The net driver's device-IRQ channel and the client virtualiser channels,
fixed by the `.system` XML at build time. Placeholder ids for the skeleton. -/
def chDriver : Channel := 0
def chIrq    : Channel := 1

/-- TRUSTED: signal a badged notification on `ch` now (`microkit_notify`). -/
@[extern "microkit_notify"]
opaque microkitNotify (ch : Channel) : IO Unit

/-- TRUSTED: defer the signal to the next return-to-kernel
(`microkit_deferred_notify`) — the batched fast path. -/
@[extern "microkit_deferred_notify"]
opaque microkitDeferredNotify (ch : Channel) : IO Unit

/-- TRUSTED: acknowledge the device IRQ (`microkit_irq_ack`). -/
@[extern "microkit_irq_ack"]
opaque microkitIrqAck (ch : Channel) : IO Unit

/-! ## sDDF net-queue ops (TRUSTED imports)

The `sddf` net queue library. `dequeue` moves the consumer head forward and
returns the descriptor it passed; `enqueue` writes a descriptor at the producer
tail and advances it. Each returns whether the ring was empty / full — the
producer NEVER writes past a full ring (it drops at the device instead), which is
exactly why no completion is ever silently lost on this path. -/

/-- TRUSTED: initialise the RX/TX handles over the shared region
(`net_queue_init`). Returns the PD's ring context. -/
@[extern "sel4_net_ctx_init"]
opaque netCtxInit : IO NetCtx

/-- TRUSTED: dequeue a filled buffer from the RX active ring
(`net_dequeue_active`). `none` when empty. -/
@[extern "sel4_net_dequeue_active_rx"]
opaque rxDequeueActive (ctx : NetCtx) : IO (Option BuffDesc)

/-- TRUSTED: return an emptied buffer to the RX free ring
(`net_enqueue_free`) — the buffer-recycle edge. -/
@[extern "sel4_net_enqueue_free_rx"]
opaque rxEnqueueFree (ctx : NetCtx) (d : BuffDesc) : IO Unit

/-- TRUSTED: acquire a TX free buffer to fill (`net_dequeue_free`). `none` when
the driver has not returned any. -/
@[extern "sel4_net_dequeue_free_tx"]
opaque txDequeueFree (ctx : NetCtx) : IO (Option BuffDesc)

/-- TRUSTED: post a filled buffer on the TX active ring for transmission
(`net_enqueue_active`). -/
@[extern "sel4_net_enqueue_active_tx"]
opaque txEnqueueActive (ctx : NetCtx) (d : BuffDesc) : IO Unit

/-- TRUSTED: read `len` bytes at `off` from the shared DMA data region into a
Lean `ByteArray`. This is the one copy off the device buffer into the reactor's
value world; the descriptor stays owned by the ring. -/
@[extern "sel4_net_data_read"]
opaque dataRead (ctx : NetCtx) (off : UInt64) (len : UInt16) : IO ByteArray

/-- TRUSTED: write `bytes` into the data region at `off`, returning the filled
length to stamp into the outgoing descriptor. -/
@[extern "sel4_net_data_write"]
opaque dataWrite (ctx : NetCtx) (off : UInt64) (bytes : ByteArray) : IO UInt16

/-! ## The crossing onto the proven core (pure)

`serviceOne` is the single point where the seL4 IO shell touches the sacred
reactor. It is pure: bytes in, bytes + advanced observation state out. It is
*definitionally* the same call `Arena.Orb.main` runs over stdin, so the H1/h2c
fork, the security gates, and every codec lane are the deployed engine unchanged.
The IO shell around it (below) only moves descriptors on and off the sDDF rings. -/

/-- The proven step for one received datagram: `Reactor.Ingress.deployStepIngress`
verbatim. The socket is gone; the bytes arrived via an sDDF RX buffer instead. -/
def serviceOne (obs : Reactor.Observe.ObsState) (input : Bytes) :
    Bytes × Reactor.Observe.ObsState :=
  Reactor.Ingress.deployStepIngress obs input

/-! ## The net PD entry points (EXPORTS — the untrusted IO shell)

These are the symbols the generated Microkit `main` dispatches to. Their bodies
are tested, not proven: they are the environment the proven core runs inside.

NOTE ON THE C ABI. A Lean `IO` function compiles to a C symbol taking an extra
`lean_object*` world token, so these are not directly Microkit's `void
notified(microkit_channel)`. The seL4 image carries a thin C trampoline —
`void notified(microkit_channel ch){ l_IoSel4_notified(ch, lean_io_mk_world()); }`
— generated alongside the CapDL init. That trampoline is part of the TRUSTED shell
and is described in `SEL4-IO-README.md`; it is not Lean and cannot be built here. -/

/-- Drain the RX active ring: for each filled buffer, copy its bytes, run the
proven step, transmit the response, and recycle the RX buffer to the free ring.
`obs` threads the reactor observation state across datagrams within one wake. -/
partial def drainRx (ctx : NetCtx) (obs : Reactor.Observe.ObsState) :
    IO Reactor.Observe.ObsState := do
  match ← rxDequeueActive ctx with
  | none => pure obs
  | some rxDesc =>
    -- 1. copy the received bytes out of the device buffer.
    let inBytes ← dataRead ctx rxDesc.ioOrOffset rxDesc.len
    -- 2. THE PROVEN CORE: one request in, one response out.
    let (out, obs') := serviceOne obs inBytes.toList
    -- 3. transmit the response, if the driver has a TX buffer for us.
    match ← txDequeueFree ctx with
    | some txDesc =>
      let n ← dataWrite ctx txDesc.ioOrOffset (ByteArray.mk out.toArray)
      txEnqueueActive ctx { txDesc with len := n }
      microkitDeferredNotify chDriver
    | none => pure ()  -- no TX buffer: drop the response (tested backpressure path)
    -- 4. recycle the RX buffer — the buffer-lease release edge.
    rxEnqueueFree ctx rxDesc
    drainRx ctx obs'

/-- Microkit `init`: build the ring context and lend all RX buffers to the driver.
In the real image `netCtxInit` also primes the RX free ring; the returned context
is stashed in PD-global state (omitted in this skeleton). -/
@[export IoSel4_init]
def init : IO Unit := do
  let _ctx ← netCtxInit
  pure ()

/-- Microkit `notified`: the net PD was signalled. On the driver/IRQ channel we
drain the RX ring through the proven core; then ack the IRQ. `ObsState.init` here
stands in for the PD-global observation state a real image threads across wakes. -/
@[export IoSel4_notified]
def notified (ch : Channel) : IO Unit := do
  let ctx ← netCtxInit
  if ch == chDriver ∨ ch == chIrq then
    let _ ← drainRx ctx Reactor.Observe.ObsState.init
    microkitIrqAck chIrq
  pure ()

/-- Microkit `protected`: a synchronous PPC into the net PD (e.g. a control-plane
query from the app PD). The net PD exposes no protected procedures on the data
path; the skeleton returns immediately. -/
@[export IoSel4_protected]
def «protected» (_ch : Channel) : IO Unit :=
  pure ()

/-! # Refinement: the sDDF ring is the Uring LTS under the seL4 IPC discipline

`Uring/` proves a submission/completion ring with a *fully demonic* kernel
environment: the environment may complete in any order, deliver on any published
free entry, exhaust at any moment, and overflow. The sDDF net ring is a STRICTLY
SMALLER labelled transition system — it is that same ring with the environment
restricted to what Microkit IPC and a NIC-cap-only driver PD can do:

  * ONE stream. There is a single standing multishot receive — the NIC RX path —
    on one fd. `Uring.OpKind.oneshot`, `.close`, and link chains (`Sqe.pred`) do
    not occur.
  * NO silent drop. The producer (driver) checks ring-full before every enqueue
    and drops the packet AT THE DEVICE when the active ring is full — no buffer id
    is ever bound to a dropped completion. That is the `.exhaust` / `.starve` edge
    (no `free` entry consumed), never the overflow-drop edge. Equivalently: the
    sDDF ring is the `nodrop = true` instance, and `dropped` stays `0`.
  * IPC-ordered environment. The driver can only act when scheduled by seL4 and
    can only touch head/tail through the CapDL-mapped shared region, signalled by
    `notified`. This makes the sDDF environment a *subset* of the demonic Uring
    environment — strictly fewer reachable interleavings.

Because the Uring theorems are proven against the demonic SUPERSET, they hold a
fortiori on the restricted sDDF sub-LTS: proving against more interleavings only
strengthens the result (see `Uring/Lts.lean`). The mapping below makes the
abstraction concrete and states the one embedding obligation the real seL4 slice
must discharge to transport the theorems. -/

/-- sDDF RX ring occupancy from the net PD's view — the four places a NIC RX
buffer id can be, plus the standing-receive bookkeeping:

  * `rxFree`   — lent to the driver (in the RX free ring, tail published);
  * `pending`  — recycled by us, RX-free tail not yet advanced;
  * `held`     — dequeued from RX active, being processed by the reactor;
  * `rxActive` — filled by the driver, not yet dequeued by us.

`armed`/`recvId`/`nextId`/`fd` track the *single standing multishot receive* on
the RX fd — the one op that the whole sDDF RX path runs on. `armed` is whether
that op is in flight; `recvId` is its `user_data` token; `nextId` mirrors the
Uring client counter (so a re-arm gets a fresh token); `fd` is the RX socket.
Because the sDDF driver drops at the device rather than binding a buffer to a
lost completion, no `ENOBUFS`/bufferless/stream-final edge ever fires here: the
receive stays armed and every delivery carries the more-flag.

`BuffDesc`s are identified with their buffer id (their data-region slot index)
as `Uring.Bid`. -/
structure RxState where
  cap      : Nat
  fd       : Uring.Fd
  nextId   : Uring.OpId
  armed    : Bool
  recvId   : Uring.OpId
  rxFree   : List Uring.Bid
  pending  : List Uring.Bid
  held     : List Uring.Bid
  rxActive : List Uring.Bid
deriving Repr, Inhabited

/-- The Uring config the sDDF ring instantiates: `nbufs` = ring capacity, the
completion capacity is the same ring, and `nodrop` is `true` (the driver never
overflows the active ring — it drops at the device). `Uring.conservation`
requires exactly this `nodrop = true`. -/
def toUringCfg (r : RxState) : Uring.Cfg :=
  { nbufs := r.cap, cqCap := r.cap, nodrop := true }

/-- Abstraction function: an sDDF RX occupancy as a `Uring.St`.

  * RX free  ↦ `free` (published free buffer entries);
  * pending  ↦ `pending` (recycled, tail not advanced);
  * held     ↦ `held` (leases the client holds);
  * RX active↦ the completion queue, each filled buffer a `.buf b` lease riding an
    unreaped completion of the single standing multishot (id `recvId`, more-flag
    set);
  * the standing receive ↦ `inflight` (`[⟨recvId, recvMulti fd, none⟩]` when
    `armed`, else `[]`).

`ovf`, `dropped`, and `dead` are empty/zero on this path: no overflow retention,
no drop, no killed stream. -/
def toUringSt (r : RxState) : Uring.St :=
  { nextId   := r.nextId
    inflight := if r.armed then [⟨r.recvId, .recvMulti r.fd, none⟩] else []
    cq       := r.rxActive.map (fun b => ⟨r.recvId, .buf b, true⟩)
    ovf      := []
    dropped  := 0
    free     := r.rxFree
    pending  := r.pending
    held     := r.held
    dead     := [] }

/-- The abstraction is faithful on the buffer multiset: the Uring `owned` count of
a bid under `toUringSt` is exactly its count across the four sDDF locations. This
is the bridge that lets `Uring.conservation` speak about sDDF buffers. Proven — no
`sorry` — because `cqBids` of the mapped active ring is the active ring itself
(the completion op id `recvId` carries no bid). -/
theorem owned_toUringSt (r : RxState) (b : Uring.Bid) :
    (Uring.owned (toUringSt r)).count b
      = (r.rxFree ++ r.pending ++ r.held ++ r.rxActive).count b := by
  have hcq : Uring.cqBids (r.rxActive.map (fun b => (⟨r.recvId, .buf b, true⟩ : Uring.Cqe)))
      = r.rxActive := by
    induction r.rxActive with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, Uring.cqBids_cons, Uring.Payload.bid?,
        Option.toList, ih, List.cons_append, List.nil_append]
  simp [Uring.owned, toUringSt, hcq, List.count_append]

/-! ## The sDDF RX LTS — the full ring, all constructors

`SddfStep` is the sDDF net RX ring as the sub-LTS of `Uring.Step` reachable under
the seL4 IPC discipline and a NIC-cap-only driver PD:

  * `submit`  — arm the single standing multishot receive (the RX path's only op);
  * `deliver` — the driver binds a published RX-free buffer and posts it on the RX
    active ring, more-flag set (the lease-granting event);
  * `reap`    — the client dequeues the RX-active head into a held lease;
  * `recycle` — the client returns a held buffer to the RX-free publication queue;
  * `publish` — the client advances the RX-free tail, publishing all pending.

There is no `complete`/`flush`/link edge (no one-shot ops, no overflow — the
driver checks ring-full and drops at the device, so no bid is ever bound to a
dropped or retained completion), and no `starve`/`exhaust`/stream-final edge (the
receive never terminates on this path; a device-side drop consumes no free entry
and produces no completion). Each constructor mirrors its like-named `Uring.Step`
twin exactly at `toUringSt`; that is `sddf_full_refinement` below. -/
inductive SddfStep : RxState → Uring.Lbl → RxState → Prop where
  /-- CLIENT: arm the standing multishot receive. Enabled only when nothing is in
  flight (`armed = false`) and no active buffers linger (`rxActive = []`); the op
  takes the fresh token `nextId`. Mirrors `Uring.Step.submit`. -/
  | submit {r : RxState}
      (harmed : r.armed = false) (hactive : r.rxActive = []) :
      SddfStep r (.submit ⟨r.nextId, .recvMulti r.fd, none⟩)
        { r with armed := true, recvId := r.nextId, nextId := r.nextId + 1 }
  /-- ENV (driver): bind a published RX-free buffer `b` and post it on the RX
  active ring with the more-flag set. Enabled while armed and the active ring has
  room (`rxActive.length < cap`) — the driver never overflows it. Mirrors
  `Uring.Step.deliver_more`. -/
  | deliver {r : RxState} {b : Uring.Bid} {f₁ f₂ : List Uring.Bid}
      (harmed : r.armed = true) (hroom : r.rxActive.length < r.cap)
      (hfree : r.rxFree = f₁ ++ b :: f₂) :
      SddfStep r (.deliver r.fd b true)
        { r with rxFree := f₁ ++ f₂, rxActive := r.rxActive ++ [b] }
  /-- CLIENT: dequeue the RX-active head into a held lease. Mirrors
  `Uring.Step.reap` dispatching a `.buf` completion. -/
  | reap {r : RxState} {b : Uring.Bid} {rest : List Uring.Bid}
      (hactive : r.rxActive = b :: rest) :
      SddfStep r (.reap ⟨r.recvId, .buf b, true⟩)
        { r with rxActive := rest, held := b :: r.held }
  /-- CLIENT: return a held RX buffer to the RX-free publication queue (write the
  ring entry, tail not yet advanced). Mirrors `Uring.Step.recycle`. -/
  | recycle {r : RxState} {b : Uring.Bid} {h₁ h₂ : List Uring.Bid}
      (hheld : r.held = h₁ ++ b :: h₂) :
      SddfStep r (.recycle b) { r with held := h₁ ++ h₂, pending := b :: r.pending }
  /-- CLIENT: advance the RX-free tail, publishing all pending entries to the
  driver. Mirrors `Uring.Step.publish`. -/
  | publish {r : RxState} :
      SddfStep r .publish { r with rxFree := r.rxFree ++ r.pending, pending := [] }

/-- The static ring capacity is a step invariant (no constructor touches `cap`).
This keeps `toUringCfg` constant along a trace, so a single Uring `Cfg` covers the
whole embedded trace. -/
theorem SddfStep.cap_eq {r r' : RxState} {l : Uring.Lbl} (h : SddfStep r l r') :
    r'.cap = r.cap := by cases h <;> rfl

/-- **The refinement, all constructors.** Every `SddfStep` is its like-named
`Uring.Step` twin at `toUringSt` — the demonic superset embeds the restricted sDDF
ring step-for-step. Discharged for every constructor (the adversarial `make-real`
audit rejected the earlier recycle-only stub). This is the load-bearing embedding
that carries `Uring.conservation`/`no_leak`/`reachable_count_le_one`/
`recycle_at_most_once` onto the seL4 sDDF path by restriction, not re-proof. -/
theorem sddf_full_refinement (r r' : RxState) (l : Uring.Lbl) (hstep : SddfStep r l r') :
    Uring.Step (toUringCfg r) (toUringSt r) l (toUringSt r') := by
  cases hstep with
  | submit harmed hactive =>
    have hstate :
        toUringSt { r with armed := true, recvId := r.nextId, nextId := r.nextId + 1 }
          = { toUringSt r with
                inflight := ⟨r.nextId, .recvMulti r.fd, none⟩ :: (toUringSt r).inflight,
                nextId := (toUringSt r).nextId + 1 } := by
      simp [toUringSt, harmed, hactive]
    rw [hstate]
    exact Uring.Step.submit (by simp [toUringSt])
      (by simp [toUringSt, Uring.kindOk, harmed]) (by simp [Uring.predOk])
  | deliver harmed hroom hfree =>
    rename_i b f₁ f₂
    have hq : (⟨r.recvId, Uring.OpKind.recvMulti r.fd, none⟩ : Uring.Sqe)
        ∈ (toUringSt r).inflight := by simp [toUringSt, harmed]
    have hfree' : (toUringSt r).free = f₁ ++ b :: f₂ := by simpa [toUringSt] using hfree
    have hcond : (({ toUringSt r with free := f₁ ++ f₂ } : Uring.St)).cq.length
        < (toUringCfg r).cqCap := by
      simp [toUringSt, toUringCfg, List.length_map]; exact hroom
    have key : Uring.post (toUringCfg r) { toUringSt r with free := f₁ ++ f₂ }
          ⟨r.recvId, .buf b, true⟩
        = toUringSt { r with rxFree := f₁ ++ f₂, rxActive := r.rxActive ++ [b] } := by
      unfold Uring.post
      rw [if_pos hcond]
      simp [toUringSt, List.map_append]
    rw [← key]
    exact Uring.Step.deliver_more hq rfl hfree'
  | reap hactive =>
    rename_i b rest
    have hcq : (toUringSt r).cq
        = ⟨r.recvId, .buf b, true⟩ :: rest.map (fun x => (⟨r.recvId, .buf x, true⟩ : Uring.Cqe)) := by
      simp [toUringSt, hactive]
    have key : Uring.dispatch
          { toUringSt r with cq := rest.map (fun x => (⟨r.recvId, .buf x, true⟩ : Uring.Cqe)) }
          ⟨r.recvId, .buf b, true⟩
        = toUringSt { r with rxActive := rest, held := b :: r.held } := by
      simp [Uring.dispatch, toUringSt]
    rw [← key]
    exact Uring.Step.reap hcq
  | recycle hheld =>
    rename_i b h₁ h₂
    have hstate :
        toUringSt { r with held := h₁ ++ h₂, pending := b :: r.pending }
          = { toUringSt r with held := h₁ ++ h₂, pending := b :: (toUringSt r).pending } := by
      simp [toUringSt]
    rw [hstate]
    exact Uring.Step.recycle (by simpa [toUringSt] using hheld)
  | publish =>
    have hstate :
        toUringSt { r with rxFree := r.rxFree ++ r.pending, pending := [] }
          = { toUringSt r with free := (toUringSt r).free ++ (toUringSt r).pending, pending := [] } := by
      simp [toUringSt]
    rw [hstate]
    exact Uring.Step.publish

/-! ## From sDDF traces to Uring reachability, and the transported theorems -/

/-- Finite traces of the sDDF RX LTS. -/
inductive SddfTrace : RxState → List Uring.Lbl → RxState → Prop where
  | nil {r : RxState} : SddfTrace r [] r
  | cons {r r' r'' : RxState} {l : Uring.Lbl} {ls : List Uring.Lbl}
      (h : SddfStep r l r') (t : SddfTrace r' ls r'') : SddfTrace r (l :: ls) r''

theorem SddfTrace.cap_eq {r r' : RxState} {ls : List Uring.Lbl}
    (t : SddfTrace r ls r') : r'.cap = r.cap := by
  induction t with
  | nil => rfl
  | cons h _ ih => rw [ih]; exact SddfStep.cap_eq h

/-- Every sDDF trace embeds as a Uring trace at `toUringSt`, under the constant
config `toUringCfg r` (capacity is invariant). -/
theorem sddf_trace_refines {r r' : RxState} {ls : List Uring.Lbl}
    (t : SddfTrace r ls r') :
    Uring.Trace (toUringCfg r) (toUringSt r) ls (toUringSt r') := by
  induction t with
  | nil => exact .nil
  | @cons r₀ rmid rfin l ls h _ ih =>
    have hcfg : toUringCfg rmid = toUringCfg r₀ := by
      simp [toUringCfg, SddfStep.cap_eq h]
    exact .cons (sddf_full_refinement _ _ _ h) (hcfg ▸ ih)

/-- The sDDF RX initial state: all buffers published to the driver's free ring,
receive not yet armed. Its abstraction is exactly `Uring.init`. -/
def rxInit (n : Nat) (fd : Uring.Fd) : RxState :=
  { cap := n, fd := fd, nextId := 0, armed := false, recvId := 0
    rxFree := List.range n, pending := [], held := [], rxActive := [] }

theorem toUringSt_rxInit (n : Nat) (fd : Uring.Fd) :
    toUringSt (rxInit n fd) = Uring.init (toUringCfg (rxInit n fd)) := by
  simp [toUringSt, rxInit, Uring.init, toUringCfg]

/-- Reachability in the sDDF RX LTS from some initial ring. -/
def SddfReachable (r : RxState) : Prop :=
  ∃ n fd ls, SddfTrace (rxInit n fd) ls r

/-- Every sDDF-reachable state abstracts to a Uring-reachable state — the bridge
that opens the whole Uring theorem suite on the sDDF path. -/
theorem sddf_uring_reachable {r : RxState} (h : SddfReachable r) :
    Uring.Reachable (toUringCfg r) (toUringSt r) := by
  obtain ⟨n, fd, ls, t⟩ := h
  have htr := sddf_trace_refines t
  have hcfg : toUringCfg (rxInit n fd) = toUringCfg r := by
    simp [toUringCfg, SddfTrace.cap_eq t]
  rw [toUringSt_rxInit, hcfg] at htr
  exact ⟨ls, htr⟩

/-- **sDDF conservation** — transported `Uring.conservation`. In every reachable
sDDF RX state, every buffer id of the universe inhabits exactly one of the four
locations (free / pending / held / active). -/
theorem sddf_conservation {r : RxState} (h : SddfReachable r) (b : Uring.Bid) :
    (r.rxFree ++ r.pending ++ r.held ++ r.rxActive).count b
      = if b < r.cap then 1 else 0 := by
  have hu := Uring.conservation (cfg := toUringCfg r) rfl (sddf_uring_reachable h) b
  rw [owned_toUringSt] at hu
  simpa [toUringCfg] using hu

/-- **sDDF no-leak** — transported `Uring.no_leak`. No RX buffer is ever lost:
every id of the universe is always recoverable in some location. -/
theorem sddf_no_leak {r : RxState} {b : Uring.Bid}
    (h : SddfReachable r) (hb : b < r.cap) :
    b ∈ (r.rxFree ++ r.pending ++ r.held ++ r.rxActive) := by
  have hc := sddf_conservation h b
  rw [if_pos hb] at hc
  exact List.count_pos_iff.mp (by omega)

/-- **sDDF recycle-at-most-once** — transported `Uring.recycle_at_most_once`.
Between any two recycles of the same RX buffer, the driver delivers it afresh;
hence each lease is returned to the free ring at most once, over every IPC-ordered
interleaving. -/
theorem sddf_recycle_at_most_once {n : Nat} {fd : Uring.Fd} {b : Uring.Bid}
    {rfin : RxState} {m₁ m₂ m₃ : List Uring.Lbl}
    (t : SddfTrace (rxInit n fd)
      (m₁ ++ .recycle b :: (m₂ ++ .recycle b :: m₃)) rfin) :
    ∃ fd' more, Uring.Lbl.deliver fd' b more ∈ m₂ := by
  have htr := sddf_trace_refines t
  rw [toUringSt_rxInit] at htr
  exact Uring.recycle_at_most_once htr

/-! ## The TX ring — the same LTS by relabeling

The TX path carries the same buffer-lease structure the *other* way round: the
client acquires a driver-returned buffer, fills it, posts it on the TX active
ring, and publishes the tail; the driver transmits and returns the buffer. That
is the RX LTS with the four locations relabeled, so the whole refinement — and
with it conservation / no-leak / recycle-at-most-once — transports with **no
re-proof**. `TxState.view` is the relabeling; the Uring slots line up as:

  * `txActive` (posted+published, driver transmitting) ↦ Uring `free`;
  * `posting`  (posted to active ring, tail not advanced) ↦ Uring `pending`;
  * `filling`  (dequeued from TX-free, client filling) ↦ Uring `held`;
  * `txFree`   (driver-returned, unclaimed — the lease grant) ↦ Uring `cq`.

The abstract TX init places all buffers in `txActive` (driver-side, matching
`Uring.init`'s `free`); a concrete client-owns-all init is a relabeled reachable
state and conserves by the same theorem. -/
structure TxState where
  cap      : Nat
  fd       : Uring.Fd
  nextId   : Uring.OpId
  armed    : Bool
  recvId   : Uring.OpId
  txActive : List Uring.Bid
  posting  : List Uring.Bid
  filling  : List Uring.Bid
  txFree   : List Uring.Bid
deriving Repr, Inhabited

/-- The relabeling of a TX occupancy onto the RX (Uring) location scheme. -/
def TxState.view (t : TxState) : RxState :=
  { cap := t.cap, fd := t.fd, nextId := t.nextId, armed := t.armed, recvId := t.recvId
    rxFree := t.txActive, pending := t.posting, held := t.filling, rxActive := t.txFree }

/-- The TX LTS, in TX-native vocabulary. Each move is one RX move under `view`. -/
inductive TxStep : TxState → Uring.Lbl → TxState → Prop where
  /-- CLIENT: arm the standing transmit-completion receive (the TX-free return
  notifications). Twin of `SddfStep.submit`. -/
  | arm {t : TxState}
      (harmed : t.armed = false) (hfree : t.txFree = []) :
      TxStep t (.submit ⟨t.nextId, .recvMulti t.fd, none⟩)
        { t with armed := true, recvId := t.nextId, nextId := t.nextId + 1 }
  /-- ENV (driver): transmit complete — return buffer `b` to the TX-free ring.
  Twin of `SddfStep.deliver`. -/
  | complete {t : TxState} {a₁ a₂ : List Uring.Bid}
      (harmed : t.armed = true) (hroom : t.txFree.length < t.cap)
      (hactive : t.txActive = a₁ ++ b :: a₂) :
      TxStep t (.deliver t.fd b true)
        { t with txActive := a₁ ++ a₂, txFree := t.txFree ++ [b] }
  /-- CLIENT: dequeue a returned buffer from the TX-free ring to fill. Twin of
  `SddfStep.reap`. -/
  | acquire {t : TxState} {rest : List Uring.Bid}
      (hfree : t.txFree = b :: rest) :
      TxStep t (.reap ⟨t.recvId, .buf b, true⟩)
        { t with txFree := rest, filling := b :: t.filling }
  /-- CLIENT: post a filled buffer on the TX active ring (tail not advanced). Twin
  of `SddfStep.recycle`. -/
  | post {t : TxState} {h₁ h₂ : List Uring.Bid}
      (hfilling : t.filling = h₁ ++ b :: h₂) :
      TxStep t (.recycle b)
        { t with filling := h₁ ++ h₂, posting := b :: t.posting }
  /-- CLIENT: advance the TX active tail, publishing all posted. Twin of
  `SddfStep.publish`. -/
  | publish {t : TxState} :
      TxStep t .publish { t with txActive := t.txActive ++ t.posting, posting := [] }

/-- Each TX move is exactly its RX twin under `view` — this is where "the RX
pattern generalizes" is discharged. -/
theorem TxStep.toRx {t t' : TxState} {l : Uring.Lbl} (h : TxStep t l t') :
    SddfStep t.view l t'.view := by
  cases h with
  | arm harmed hfree => exact SddfStep.submit harmed hfree
  | complete harmed hroom hactive => exact SddfStep.deliver harmed hroom hactive
  | acquire hfree => exact SddfStep.reap hfree
  | post hfilling => exact SddfStep.recycle hfilling
  | publish => exact SddfStep.publish

/-- **TX refinement, all constructors** — the TX ring embeds in the same Uring
LTS at `toUringSt ∘ view`. -/
theorem tx_full_refinement (t t' : TxState) (l : Uring.Lbl) (h : TxStep t l t') :
    Uring.Step (toUringCfg t.view) (toUringSt t.view) l (toUringSt t'.view) :=
  sddf_full_refinement _ _ _ h.toRx

/-- Finite traces of the TX LTS. -/
inductive TxTrace : TxState → List Uring.Lbl → TxState → Prop where
  | nil {t : TxState} : TxTrace t [] t
  | cons {t t' t'' : TxState} {l : Uring.Lbl} {ls : List Uring.Lbl}
      (h : TxStep t l t') (r : TxTrace t' ls t'') : TxTrace t (l :: ls) t''

theorem TxTrace.toRx {t t' : TxState} {ls : List Uring.Lbl}
    (tr : TxTrace t ls t') : SddfTrace t.view ls t'.view := by
  induction tr with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.toRx ih

/-- The TX initial state; its `view` is `rxInit`. -/
def txInit (n : Nat) (fd : Uring.Fd) : TxState :=
  { cap := n, fd := fd, nextId := 0, armed := false, recvId := 0
    txActive := List.range n, posting := [], filling := [], txFree := [] }

theorem txInit_view (n : Nat) (fd : Uring.Fd) : (txInit n fd).view = rxInit n fd := rfl

/-- Reachability in the TX LTS. -/
def TxReachable (t : TxState) : Prop :=
  ∃ n fd ls, TxTrace (txInit n fd) ls t

theorem tx_view_reachable {t : TxState} (h : TxReachable t) : SddfReachable t.view := by
  obtain ⟨n, fd, ls, tr⟩ := h
  exact ⟨n, fd, ls, txInit_view n fd ▸ tr.toRx⟩

/-- **TX conservation** — transported the same way. Every TX buffer inhabits
exactly one of the four TX locations in every reachable state. -/
theorem tx_conservation {t : TxState} (h : TxReachable t) (b : Uring.Bid) :
    (t.txActive ++ t.posting ++ t.filling ++ t.txFree).count b
      = if b < t.cap then 1 else 0 := by
  have hc := sddf_conservation (tx_view_reachable h) b
  simpa [TxState.view] using hc

/-! # The 6-PD Microkit assembly (structural sketch)

The net subsystem is a standard sDDF 6-PD Microkit assembly. This is data — the
Lean structures naming the PDs, their notification channels, and the shared ring /
DMA regions — plus one machine-checked wiring obligation. The concrete CapDL
`.system` image (which frames/IRQ each PD actually holds) is audited outside Lean;
what is checked here is that every wire names declared, distinct PDs. -/

/-- The six protection domains of the sDDF net subsystem. -/
inductive PdId where
  | netDriver | netVirtRx | netVirtTx | client | timer | serial
deriving DecidableEq, Repr

/-- A protection domain: an id and a Microkit scheduling priority. -/
structure Pd where
  id       : PdId
  priority : Nat
deriving Repr, DecidableEq

/-- A notification channel between two PDs, each side carrying its local slot id.
`microkit_notify`/`notified` ride these. -/
structure ChanWire where
  a   : PdId
  b   : PdId
  idA : Channel
  idB : Channel
deriving Repr, DecidableEq

/-- A shared-memory region (a ring page, or a DMA data region) mapped between a
producer PD and a consumer PD. -/
structure ShRegion where
  label    : String
  producer : PdId
  consumer : PdId
deriving Repr, DecidableEq

/-- A Microkit assembly: the PDs, their channels, and their shared regions —
i.e. the content the `.system` XML declares. -/
structure Assembly where
  pds     : List Pd
  chans   : List ChanWire
  regions : List ShRegion
deriving Repr

/-- Whether a PD id is declared in the assembly. -/
def Assembly.hasPd (asm : Assembly) (p : PdId) : Bool :=
  asm.pds.any (fun pd => pd.id == p)

/-- The concrete net subsystem: driver, RX/TX virtualisers, the reactor client,
the timer, and the serial console. Channel/region wiring is the sDDF net layout
(RX: driver→virt-rx→client; TX: client→virt-tx→driver; timer + serial as
service PDs). Priorities follow the sDDF convention (driver highest of the data
plane, virtualisers just below, client below them, timer top, serial low). -/
def netSubsystem : Assembly :=
  { pds :=
      [ ⟨.netDriver, 101⟩, ⟨.netVirtRx, 99⟩, ⟨.netVirtTx, 100⟩,
        ⟨.client, 97⟩, ⟨.timer, 150⟩, ⟨.serial, 98⟩ ]
    chans :=
      [ ⟨.netDriver, .netVirtRx, 0, 0⟩,   -- device RX → RX virtualiser
        ⟨.netVirtRx, .client,    1, 0⟩,   -- RX virtualiser → client
        ⟨.client,    .netVirtTx, 1, 0⟩,   -- client → TX virtualiser
        ⟨.netVirtTx, .netDriver, 1, 1⟩,   -- TX virtualiser → device TX
        ⟨.netDriver, .timer,     2, 0⟩,   -- driver ↔ timer (link poll / watchdog)
        ⟨.client,    .serial,    2, 0⟩ ]  -- client ↔ serial (debug console)
    regions :=
      [ ⟨"rx_free",    .client,    .netDriver⟩,   -- client lends empties to driver
        ⟨"rx_active",  .netDriver, .client⟩,      -- driver posts filled to client
        ⟨"tx_active",  .client,    .netDriver⟩,   -- client posts filled to driver
        ⟨"tx_free",    .netDriver, .client⟩,      -- driver returns emptied to client
        ⟨"rx_dma",     .netDriver, .client⟩,      -- shared RX DMA data region
        ⟨"tx_dma",     .client,    .netDriver⟩ ]} -- shared TX DMA data region

/-- Wiring well-formedness: every channel and region names declared, distinct PDs.
This is the structural half of the CapDL obligation — the part expressible in
Lean. -/
def Assembly.wellWired (asm : Assembly) : Prop :=
  (∀ c ∈ asm.chans, asm.hasPd c.a ∧ asm.hasPd c.b ∧ c.a ≠ c.b) ∧
  (∀ rg ∈ asm.regions, asm.hasPd rg.producer ∧ asm.hasPd rg.consumer ∧ rg.producer ≠ rg.consumer)

/-- The net subsystem is well-wired — machine-checked. -/
theorem netSubsystem_wellWired : netSubsystem.wellWired := by
  unfold Assembly.wellWired; decide

/-- The CapDL-init obligation for a confined net client. The `wired` component is
discharged in Lean (`netSubsystem_wellWired`); `soleNic`/`clientPresent` fix which
PD is the NIC-cap holder and that the reactor client is present. The residual — the
image granting the *device MMIO frame + IRQ to the driver alone* and *no device cap
to the client* — is audited against the concrete CapDL/`.system` image, which is
outside Lean's reach (see `SEL4-IO-README.md`); it is named here, not proven. -/
structure CapDLObligation (asm : Assembly) : Prop where
  wired         : asm.wellWired
  soleNic       : asm.hasPd PdId.netDriver = true
  clientPresent : asm.hasPd PdId.client = true

/-- The net subsystem discharges the in-Lean part of the CapDL obligation. -/
theorem netSubsystem_capDL : CapDLObligation netSubsystem :=
  { wired := netSubsystem_wellWired
    soleNic := by decide
    clientPresent := by decide }

end IoSel4
