# SEL4-IO — the seL4 Microkit / sDDF IO boundary for the net PD

This is the endgame substrate for the reactor: instead of a Linux socket accept
loop feeding bytes through the proven core, the net **protection domain** (PD)
receives packets from an sDDF NIC driver over shared descriptor rings and hands
their bytes to the exact same `Reactor.Ingress.deployStepIngress`.

**Status, stated honestly.** `IoSel4.lean` typechecks (`lake env lean IoSel4.lean`)
and compiles to an object file (`lake build IoSel4`). It **does not run here** and
does not claim to. A running net PD needs an seL4 image — the Microkit SDK, the
sDDF net driver, and a CapDL init — none of which is available in this
environment. What this directory delivers is the *typed seam* (the `@[extern]` /
`@[export]` boundary), the *refinement mapping* that carries the already-proven
`Uring` buffer-lease theorems onto the sDDF ring — **now fully discharged for both
the RX and TX rings, all constructors** — and a **structural sketch of the 6-PD
Microkit assembly** with a machine-checked wiring obligation. The C shim, the
trampoline, and the `.system`/CapDL image are scaffolded and described, not built.

---

## What a real seL4 build needs

1. **Microkit SDK** (SDK 2.2.0), providing `libmicrokit`,
   the `.system` XML compiler, and the loader that turns a set of PD ELFs + an XML
   description into a bootable image. Microkit is the seL4-native static
   partitioning framework (not CAmkES); a PD's entry surface is
   `init` / `notified(channel)` / `protected(channel, msginfo)`.

2. **The sDDF net driver + virtualisers.** The seL4 Device Driver Framework
   supplies the NIC driver PD and the RX/TX virtualiser PDs, plus the
   `net_queue` library (`net_queue_init`, `net_{en,de}queue_{free,active}`,
   `net_queue_empty_*`, `net_request_signal_*`). The net PD here is an sDDF
   *client*: it owns one RX handle and one TX handle over shared-memory regions.

3. **A CapDL init image.** The capability distribution list that hands out exactly
   the caps each PD gets: the NIC MMIO frame + IRQ to the driver, the shared ring
   pages and DMA data region between driver/virtualiser/net PD, and the
   notification channels. This is what makes the net PD a *confined, NIC-reach-only*
   PD — it has no authority beyond its rings and channels. The CapDL/`.system`
   image is **not proven** (the capability metatheory below proves the general cap
   algebra, not this particular image — see below).

4. **The Lean → seL4 toolchain hack** (an established path, reused verbatim):
   the Lean closure compiles macOS Mach-O → `leanc` → an aarch64-musl ELF with
   libuv excised, GMP cross-built, on a `sel4-musl` syscall shim. `IoSel4`'s
   module closure (Reactor + Uring + Proto) must go through that same path. This
   whole hack is deleted by a CakeML/Pancake reformalization of the closure; until
   then it is the load-bearing bridge.

---

## The 6-PD assembly (net PD is one domain)

This `.system` is a 6-PD Microkit assembly, joined PD↔PD by
`sel4-shared-ring-buffer` (the seL4-native lease):

| PD | role |
|----|------|
| **executor** (pri 120) | the heart — runs the verified `execFullForest`; BOOTS on qemu aarch64/riscv64 |
| **verifier** | Lean-free STARK checker — the minimal-TCB bankable heart |
| **persist** | durable redb commit log |
| **net** | the NIC **driver** — sole NIC cap, virtio-mmio single-queue, the device IRQ |
| **net_client** | ingress — smoltcp + TCP + a signed-turn gate → `turn_in` |
| **app** | the application |

`IoSel4.lean` is the seam that upgrades the **net_client** ingress path: today it
is smoltcp for connectivity/correctness (single-queue virtio, not line rate); the
verified reactor replaces the ingress filter with `deployStepIngress` driven by the
sDDF rings the **net** driver publishes. The net PD stays confined — its authority
is exactly its RX/TX handles and its notification channels, nothing more.

The capability metatheory proves an seL4 cap and the reactor's own capability
abstraction are the same abstraction at different distance `n`, and that a
delegation embedded as a kernel `mint` preserves both invariants — sorry-free,
l4v-pinned. What is **not** proven
there is the concrete `.system`/CapDL image, the driver, or the network path. This
IO seam is exactly that unproven network path made small and typed, with the one
data-plane invariant that *is* provable (the buffer lease) transported below.

---

## The ring-swap: io_uring LTS → sDDF LTS on the verified path

The repo already proves a submission/completion ring (`Uring/`) as a two-player
LTS with a **fully demonic** kernel environment, and its buffer-lease theorems:

- `Uring.conservation` — every buffer id inhabits exactly one location;
- `Uring.no_leak` — no buffer is ever lost;
- `Uring.reachable_count_le_one` — no buffer is double-owned;
- `Uring.recycle_at_most_once` — no buffer is returned to the free ring twice.

The sDDF net ring is the **same ring restricted to the seL4 IPC discipline** — a
strictly smaller LTS:

| Uring (Linux io_uring) | sDDF (seL4 net PD) |
|---|---|
| any op kind, link chains, close/stale edges | one standing multishot RX recv, no links, no close |
| CQ overflow → retain (`nodrop`) or silently drop | producer checks ring-full, drops **at the device** → no bid ever bound to a dropped completion; `nodrop = true`, `dropped = 0` |
| kernel shares CQ/SQ pages, arbitrary timing | driver acts only when seL4-scheduled, touches head/tail only through CapDL-mapped shared memory, signalled by `notified` |

Because the Uring theorems are proven against the demonic **superset** of
interleavings, they hold *a fortiori* on the restricted sDDF sub-LTS — proving
against more interleavings only strengthens the result.

`IoSel4.lean` makes this concrete:

- `IoSel4.RxState` — the four sDDF RX locations a buffer id can occupy (free /
  pending / held / active).
- `IoSel4.toUringSt : RxState → Uring.St` — the abstraction function (RX-free ↦
  `free`, pending ↦ `pending`, held ↦ `held`, RX-active ↦ the completion queue of
  `.buf` leases).
- `IoSel4.toUringCfg` — instantiates `nodrop = true` (the sDDF driver never
  overflows the active ring), which is exactly `Uring.conservation`'s hypothesis.
- `IoSel4.owned_toUringSt` — **proved, no `sorry`**: the Uring `owned` bid-multiset
  under `toUringSt` equals the count across the four sDDF locations. This is the
  bridge that lets the Uring theorems speak about sDDF buffers.
- `IoSel4.SddfStep` — the sDDF RX sub-LTS, defined in full: `submit` (arm the one
  standing multishot receive), `deliver` (driver binds a published free buffer,
  more-flag set), `reap`, `recycle`, `publish`. No `complete`/`flush`/link edge
  (no one-shot ops, no overflow — the driver drops at the device), and no
  `starve`/`exhaust`/stream-final edge (the receive never terminates; a device
  drop consumes no free entry and posts no completion).
- `IoSel4.sddf_full_refinement` — the embedding, **discharged for every
  constructor** (`#print axioms` ⊆ {`propext`, `Quot.sound`}). Each sDDF step *is*
  its like-named `Uring.Step` at `toUringSt`. `sddf_trace_refines` lifts it to
  traces and `sddf_uring_reachable` to reachability (capacity is a step invariant,
  so a single `Uring.Cfg` covers the trace, and `toUringSt (rxInit …) = Uring.init`).
- `IoSel4.sddf_conservation` / `sddf_no_leak` / `sddf_recycle_at_most_once` — the
  four Uring theorems, **transported and proved** on the sDDF RX path via
  `owned_toUringSt`.
- `IoSel4.TxState` / `TxStep` / `tx_full_refinement` / `tx_conservation` — the TX
  ring is the **same LTS by relabeling** (`TxState.view`): the client acquires a
  driver-returned buffer, fills, posts, publishes; the driver transmits and
  returns. The four TX locations map onto the Uring slots (txActive↦free,
  posting↦pending, filling↦held, txFree↦cq), and every RX proof transports with
  **no re-proof** — this is where "the RX pattern generalizes" is discharged.

The payoff: the Linux io_uring lease proof becomes the seL4 sDDF lease proof for
**both rings** by **restriction, not re-proof**. The memory-model / substrate
parameter (per the concurrency posture: AF_XDP → sDDF → FPGA → silicon silently
swaps the memory model) is re-instantiated at the ring boundary, not retrofitted.

### The 6-PD Microkit assembly (Lean structures)

`IoSel4` also carries the net subsystem as **data**: `PdId` (the six PDs —
`netDriver`, `netVirtRx`, `netVirtTx`, `client`, `timer`, `serial`), `Pd`
(id + Microkit priority), `ChanWire` (a notification channel with each side's local
slot id), `ShRegion` (a shared ring / DMA region with producer + consumer), and
`Assembly` bundling them. `netSubsystem : Assembly` fixes the standard sDDF
layout — RX `driver→virt-rx→client`, TX `client→virt-tx→driver`, plus the four
ring regions and two DMA data regions.

The **CapDL-init obligation** is `CapDLObligation`. Its structural half —
`Assembly.wellWired`, that every channel and region names declared, distinct PDs —
is **machine-checked** (`netSubsystem_wellWired`, `netSubsystem_capDL`, both by
`decide`, `#print axioms` = {`propext`}). The residual — the concrete image granting
the *device MMIO frame + IRQ to the driver alone* and *no device cap to the
client* — is a property of the CapDL/`.system` image, outside Lean's reach; it is
**named** in `CapDLObligation`, not proven, and audited on the image.

---

## The boundary declarations (what is TRUSTED)

Two families in `IoSel4.lean`:

- **IMPORTS** (`@[extern]`, TRUSTED foreign code, no Lean body): the Microkit
  primitives (`microkit_notify`, `microkit_deferred_notify`, `microkit_irq_ack`)
  and the sDDF net-queue ops (`sel4_net_dequeue_active_rx`,
  `sel4_net_enqueue_free_rx`, `sel4_net_dequeue_free_tx`,
  `sel4_net_enqueue_active_tx`, `sel4_net_data_{read,write}`, `sel4_net_ctx_init`).
  These are C in the seL4 image; the Lean side treats them as an axiomatic
  boundary. The reactor theorems are stated *relative* to their contract.

- **EXPORTS** (`@[export]`, the entry points the untrusted IO shell provides):
  `IoSel4_init`, `IoSel4_notified`, `IoSel4_protected`. Their bodies drain the RX
  ring, and the one line that crosses onto the sacred core is `IoSel4.serviceOne`
  = `Reactor.Ingress.deployStepIngress` verbatim — the same call `Arena.Orb.main`
  runs over stdin. Everything around it (dequeue → copy → step → enqueue → recycle)
  is the tested-not-proven environment.

### The C ABI trampoline (part of the TRUSTED shell, not buildable here)

A Lean `IO` function compiles to a C symbol taking an extra `lean_object*` world
token, so the exports are **not** directly Microkit's `void notified(microkit_channel)`.
The seL4 image carries a thin C trampoline generated alongside the CapDL init:

```c
/* generated glue in the net PD's crt — TRUSTED, ~30 lines total */
#include <microkit.h>
extern lean_object *l_IoSel4_notified(uint32_t ch, lean_object *world);
extern lean_object *l_IoSel4_init(lean_object *world);
extern lean_object *l_IoSel4_protected(uint32_t ch, lean_object *world);

void init(void)                       { l_IoSel4_init(lean_io_mk_world()); }
void notified(microkit_channel ch)    { l_IoSel4_notified((uint32_t)ch, lean_io_mk_world()); }
microkit_msginfo protected(microkit_channel ch, microkit_msginfo mi) {
  l_IoSel4_protected((uint32_t)ch, lean_io_mk_world());
  return microkit_msginfo_new(0, 0);
}
```

The sDDF/Microkit symbols the `@[extern]` decls name resolve at the **final seL4
link** (linking the Lean-emitted `.o`, `libmicrokit`, and the sDDF net-queue lib
into the net PD ELF). That link is not available in this environment, which is why
`IoSel4` is a `[[lean_lib]]` (compiles to `.o`, no executable link) and not a
`lean_exe`.

---

## Build here vs. what a real target needs

| step | here | real seL4 target |
|---|---|---|
| `lake env lean IoSel4.lean` (typecheck) | ✅ runs, clean | ✅ |
| `lake build IoSel4` (elaborate → `.o` → archive) | ✅ runs, clean | ✅ |
| `owned_toUringSt` (faithfulness lemma) | ✅ proved, no `sorry` | ✅ |
| `sddf_full_refinement` (RX, all constructors) | ✅ proved, no `sorry` | ✅ |
| `sddf_conservation` / `no_leak` / `recycle_at_most_once` | ✅ transported, proved | ✅ |
| `tx_full_refinement` / `tx_conservation` (TX ring) | ✅ proved, no `sorry` | ✅ |
| `netSubsystem_wellWired` / `netSubsystem_capDL` (wiring) | ✅ proved by `decide` | ✅ |
| `CapDLObligation` device-cap residual | ⛔ named, not proven | audited on the CapDL/`.system` image |
| C trampoline + sDDF/Microkit link | ⛔ not available | needs Microkit SDK + sDDF lib |
| `.system` XML + CapDL image + boot | ⛔ not available | needs the SDK loader + qemu/hardware |
