# SOCKS-CODEC — wiring the real SOCKS handshake engine into the FSM egress gate

`Reactor/Socks.lean` (module `Reactor.Socks`, namespace `Reactor`) drives the **real**
`Socks.Handshake` engine into `Proto.Config.socksFeed`, and proves the SOCKS no-early-egress
seam against the FSM's relay gating.

## Before

`Proto.Config.socksFeed : SocksPhase → Bytes → SocksOut` was an abstract field;
`Reactor.Config.demoConfig` stubbed it to `fun _ _ => .fail`. Every FSM theorem held "for
all `socksFeed`", but nothing tied the `socksHandshake` state to a proven no-early-egress
property against a *concrete* handshake engine. This closes that gap.

## The carrier: no stub reshape needed

Unlike the TLS / WebSocket lanes (whose `{id : Nat}` state stubs the seed had to reshape),
the SOCKS lane's state carrier is already real: `Proto.SocksPhase` is a genuine 4-constructor
enum, and `socksFeed : SocksPhase → Bytes → SocksOut` threads it by value (`SocksOut.progress`
returns the next phase). So no `Proto/Basic.lean` reshape was required — the real engine wires
straight into the existing field. What was missing was the *engine*, not a carrier.

## What is wired

`Socks.hstep : HState → Bytes → HState × Out` — the total deterministic SOCKS5 handshake step,
carrying the library's proven `hstep_no_early_egress` relay gate — is driven by the adapter
`socksFeedReal`:

- `toLib` / `ofLib` map the FSM `SocksPhase` ↔ library `Socks.Phase`. No `SocksPhase` maps to
  the library's `established` (established is the FSM's `plainTunnel` state, never a
  `socksHandshake` phase).
- `libConsumed` reads the consumed-byte count back from the same per-phase parser `hstep`
  uses, so the FSM drops exactly the handshake-consumed prefix.
- `socksFeedReal target hasAuth` runs `hstep` and translates its egress action:
  `wait` → `.progress` (same phase, 0 consumed); `sendAuth`/`sendConnect` → `.progress` to the
  next phase; `tunnelUp` → `.connect target` (the single door to `connectUpstream` →
  `plainTunnel`); `closeErr` → `.fail`.
- `wireSocks target hasAuth cfg` = `{ cfg with socksFeed := socksFeedReal target hasAuth }`.
- `demoSocksConfig := wireSocks ⟨0⟩ false Reactor.Config.demoConfig` — a concrete running-reactor
  config with the real engine live in `socksFeed` (`demoSocksConfig_socksFeed : … = socksFeedReal ⟨0⟩ false`, by `rfl`).

## The seam theorem — `socks_no_early_egress_seam`

For a `wireSocks`-wired config, three composed facts (and `demoSocksConfig_no_early_egress_seam`
specializes them to the concrete config):

1. **FSM structural gate** — `socksFeed_no_upstream`: while the FSM is in `socksHandshake`,
   every output `onBytes` emits is a peer `send`, a `connectUpstream`, or nothing — **never a
   `sendUpstream`** (`isUpstream o = false`). Application-byte relay to the upstream socket is
   structurally impossible in this state, for *any* `socksFeed` outcome.
2. **Library relay gate closed** — `socks_relay_gate_closed`: the real `Socks.hEgress` relay
   forwards nothing (`= []`) for every FSM handshake phase, via the library's
   `hstep_no_early_egress` (none of the `SocksPhase`s map to `established`).
3. **Tunnel opens only at `established`** — `socks_connect_reaches_established`: the wired
   `socksFeed` yields `.connect` (the sole trigger for `connectUpstream` → `plainTunnel`) **only
   when** the real `Socks.hstep` has reached `established` (via `connect_implies_tunnelUp` +
   `hstep_tunnelUp_established`, both re-derived from the real `hstep`).

Together: **no application bytes are relayed before the real SOCKS handshake reaches
`established`.** The FSM relay opens exactly with the library gate, not before.

## Honest role note (the modeling seam)

The `Socks` library models the SOCKS5 *client* handshake toward an **upstream** proxy — the
engine that governs the *egress* leg. The FSM's `socksHandshake` is the pre-tunnel stage that,
on completion, opens that egress leg (`connectUpstream` → `plainTunnel`, where `onBytes`
finally relays with `sendUpstream`). The property the seam is about — no application bytes reach
the upstream socket before the handshake is established — is exactly the egress gating the
library proves, and it is **role-agnostic** (a gating property of the phase-indexed relay).

What this wiring does **not** claim: that the library's per-phase byte *parsers* (which parse a
SOCKS *server's* responses) perform the FSM's server-ingress parse of a *client's* greeting/
request — the two differ in role. The canned peer reply is the FSM's own `socksConnectReply`,
emitted at tunnel-open, not by these parsers. The load-bearing, proved composition is the
gating; the parser role is a documented limitation, not a papered-over gap.

## Build / verification status

- `lake build Reactor.Socks` — **green**, zero `sorry`.
- `#print axioms Reactor.socks_no_early_egress_seam` (and the demo / connect variants) →
  `[propext, Quot.sound]` — within the allowed subset.
- `lake build Reactor` (the glob aggregate) currently fails on **one sibling module,
  `Reactor.Ws`** (an unsolved-goal at `Reactor/Ws.lean:364`), an in-progress
  file outside this module's scope. All other 52/54 modules, including `Reactor.Socks`, build.
- Ownership: only `Reactor/Socks.lean` (new) authored; one line `import Reactor.Socks` appended
  to `Reactor.lean`. `Proto/Basic.lean`, `Reactor/Config.lean`, `lakefile.toml` untouched.
