import Reactor.Config
import Socks.Handshake

/-!
# Reactor.Socks — wiring the real SOCKS handshake engine into the FSM egress gate

`Proto.Config.socksFeed : SocksPhase → Bytes → SocksOut` was a bare abstract field
(`Reactor.Config.demoConfig` stubbed it to `fun _ _ => .fail`). Every FSM theorem held
"for all `socksFeed`", but no *concrete* handshake engine was ever plugged in, so nothing
tied the FSM's `socksHandshake` state to a proven no-early-egress property. This file
closes that gap by driving the **real** `Socks.Handshake` engine (`Socks.hstep`, the total
deterministic SOCKS5 handshake step, with its proven `hstep_no_early_egress` relay gate).

## What is wired, and the honest role note

The `Socks` library models the SOCKS5 *client* handshake toward an **upstream** proxy: it
is the engine that governs the *egress* leg (local node → upstream). The FSM's
`socksHandshake` state is the pre-tunnel handshake stage; on completion it emits
`connectUpstream` and, once the upstream connect lands (`onUp .connected`), enters
`plainTunnel` — the state in which `onBytes` finally relays application bytes with
`sendUpstream`. So the property the seam is about — *no application bytes reach the
upstream socket before the handshake is established* — is exactly the egress-gating the
`Socks` library proves.

The load-bearing, genuinely-composed asset is that **gating**: the phase-gated relay
(`Socks.HState.up` / `Socks.hEgress` / `hstep_no_early_egress`), which is role-agnostic,
and the handshake's `tunnelUp` transition into `established`, which is the single door that
opens the gate. The adapter runs the real `Socks.hstep` to decide *when* the tunnel opens
(`SocksOut.connect`) versus stays in-handshake (`.progress`) or tears down (`.fail`). The
per-phase byte *parsers* the engine uses are the library's client-response parsers; their
role differs from a server-ingress parse, and this wiring does not claim otherwise — the
canned peer reply is the FSM's own `socksConnectReply`, emitted at tunnel-open. What is
proved here is the gating composition, which holds independent of parser role.

## The seam

`socks_no_early_egress_seam` composes three facts for a `wireSocks`-wired config:

1. **FSM structural gate** (`socksFeed_no_upstream`): while the FSM is in `socksHandshake`,
   `onBytes` emits no `sendUpstream` output — for *any* `socksFeed` outcome
   (`.progress` → a peer `send`; `.connect` → `connectUpstream`; `.fail` → close). No
   application byte is relayed upstream during the handshake.
2. **Library relay gate closed** (`socks_relay_gate_closed`): the real `Socks` relay gate
   `hEgress` forwards nothing for every phase that keeps the FSM in `socksHandshake`
   (none of the `SocksPhase`s map to `established`), via the library's
   `hstep_no_early_egress`.
3. **Tunnel opens only at `established`** (`socks_connect_reaches_established`): the wired
   `socksFeed` yields `.connect` (the sole path to `connectUpstream` → `plainTunnel`)
   *only* when the real `Socks.hstep` reaches `established` (emits `tunnelUp`). The FSM
   relay opens exactly with the library gate, not before.
-/

namespace Reactor

open Proto (Config ProtoState Output SocksPhase SocksOut Addr onBytes sendIf)

/-! ## Phase correspondence: FSM `SocksPhase` ↔ library `Socks.Phase` -/

/-- Map the FSM's server-facing handshake phase onto the library's handshake phase, so the
real `Socks.hstep` can drive the lane. No `SocksPhase` maps to `established` — established
is represented FSM-side by the `plainTunnel` state, never by a `socksHandshake` phase. -/
def toLib : SocksPhase → Socks.Phase
  | .versionDetect  => .awaitGreeting
  | .s5AwaitAuth    => .awaitAuth
  | .s5AwaitRequest => .awaitReply
  | .s4Parsing      => .awaitGreeting

/-- Map the library's handshake phase back to an FSM `SocksPhase` (used to report the next
`.progress` phase). The two terminal library phases never appear on the `.progress` path
(`established` → `.connect`, `failed` → `.fail`); they are mapped for totality only. -/
def ofLib : Socks.Phase → SocksPhase
  | .awaitGreeting => .versionDetect
  | .awaitAuth     => .s5AwaitAuth
  | .awaitReply    => .s5AwaitRequest
  | .established   => .s5AwaitRequest
  | .failed        => .versionDetect

/-- Bytes the current library phase consumes on a complete parse — read back from the same
per-phase parser `Socks.hstep` uses, so the FSM drops exactly the handshake-consumed
prefix. `0` when the parse is incomplete/errored (the FSM keeps the accumulation intact). -/
def libConsumed : Socks.Phase → List UInt8 → Nat
  | .awaitGreeting, buf =>
    match Socks.parseMethod buf with | .complete _ c => c | _ => 0
  | .awaitAuth, buf =>
    match Socks.parseAuthStatus buf with | .complete _ c => c | _ => 0
  | .awaitReply, buf =>
    match Socks.parseReply buf with | .complete _ c => c | _ => 0
  | _, _ => 0

/-! ## The adapter: real `Socks.hstep` → FSM `SocksOut` -/

/-- The `socksFeed` adapter. It runs the **real** `Socks.hstep` on the phase/buffer and
translates the handshake's egress action into the FSM's `SocksOut`:

* `wait` (need more bytes) → `.progress` with the same phase and `0` consumed;
* `sendAuth` / `sendConnect` (handshake advances) → `.progress` to the next phase, consuming
  the parsed prefix; the peer reply is left empty (the FSM sends its canned
  `socksConnectReply` at tunnel-open, not mid-handshake);
* `tunnelUp` (handshake established) → `.connect target` — the single door to
  `connectUpstream` → `plainTunnel`;
* `closeErr` → `.fail` (the FSM closes).

`target` is the upstream this SOCKS listener opens toward; `hasAuth` selects the
username/password branch of the real handshake. -/
def socksFeedReal (target : Addr) (hasAuth : Bool)
    (phase : SocksPhase) (buf : List UInt8) : SocksOut :=
  match (Socks.hstep ⟨toLib phase, hasAuth⟩ buf).2 with
  | .wait        => .progress phase 0 []
  | .sendAuth    =>
    .progress (ofLib (Socks.hstep ⟨toLib phase, hasAuth⟩ buf).1.phase)
      (libConsumed (toLib phase) buf) []
  | .sendConnect =>
    .progress (ofLib (Socks.hstep ⟨toLib phase, hasAuth⟩ buf).1.phase)
      (libConsumed (toLib phase) buf) []
  | .tunnelUp    => .connect target (libConsumed (toLib phase) buf)
  | .closeErr    => .fail

/-- The config transformer: replace the (stubbed) `socksFeed` field with the real-engine
adapter, leaving every other lane untouched. -/
def wireSocks (target : Addr) (hasAuth : Bool) (cfg : Config) : Config :=
  { cfg with socksFeed := socksFeedReal target hasAuth }

/-- A concrete running-reactor config with the real SOCKS handshake engine wired into
`socksFeed`, over the HTTP/1.1 demo config. Opens toward the upstream identified by
`⟨0⟩` with no client auth. -/
def demoSocksConfig : Config := wireSocks ⟨0⟩ false Reactor.Config.demoConfig

/-- The wired config's `socksFeed` is exactly the real-engine adapter. -/
theorem wireSocks_socksFeed (target : Addr) (hasAuth : Bool) (cfg : Config) :
    (wireSocks target hasAuth cfg).socksFeed = socksFeedReal target hasAuth := rfl

/-- `demoSocksConfig` drives the real `Socks.hstep`, not the `.fail` stub. -/
theorem demoSocksConfig_socksFeed :
    demoSocksConfig.socksFeed = socksFeedReal ⟨0⟩ false := rfl

/-! ## `true` exactly on upstream-relay outputs -/

/-- The discriminator for an application-byte relay to the upstream socket. The FSM relays
application bytes only via `Output.sendUpstream`; `send` targets the *peer* (client). -/
def isUpstream : Output → Bool
  | .sendUpstream _ _ => true
  | _ => false

/-! ## (1) FSM structural gate: no upstream relay while handshaking -/

/-- **No application bytes are relayed upstream during the SOCKS handshake.** For any
config and any `socksFeed` outcome, every output `onBytes` emits from the `socksHandshake`
state is a peer `send`, a `connectUpstream`, or nothing — never a `sendUpstream`. Relay to
the upstream socket is structurally impossible in this state; it can only begin after the
FSM has left for `plainTunnel`. -/
theorem socksFeed_no_upstream (cfg : Config) (buf : List UInt8)
    (phase : SocksPhase) (data : List UInt8) :
    ∀ o ∈ (onBytes cfg (.socksHandshake buf phase) data).outs, isUpstream o = false := by
  intro o ho
  cases hf : cfg.socksFeed phase (buf ++ data) with
  | progress p' c reply =>
    have hout : (onBytes cfg (.socksHandshake buf phase) data).outs = sendIf reply := by
      simp [onBytes, hf]
    rw [hout] at ho
    unfold sendIf at ho
    split at ho
    · exact absurd ho (List.not_mem_nil o)
    · simp only [List.mem_singleton] at ho; subst ho; rfl
  | connect addr c =>
    have hout : (onBytes cfg (.socksHandshake buf phase) data).outs
        = [Output.connectUpstream addr] := by simp [onBytes, hf]
    rw [hout] at ho
    simp only [List.mem_singleton] at ho; subst ho; rfl
  | fail =>
    have hout : (onBytes cfg (.socksHandshake buf phase) data).outs = [] := by
      simp [onBytes, hf]
    rw [hout] at ho
    exact absurd ho (List.not_mem_nil o)

/-! ## (2) Library relay gate closed for every handshake phase -/

/-- **The real SOCKS relay gate is closed for every FSM handshake phase.** No `SocksPhase`
maps to the library's `established`, so `Socks.hstep_no_early_egress` gives `hEgress = []`:
the proven relay forwards no application bytes, in either direction, while the FSM is in
`socksHandshake`. -/
theorem socks_relay_gate_closed (phase : SocksPhase) (hasAuth : Bool)
    (dir : Socks.Dir) (app : List UInt8) :
    Socks.hEgress ⟨toLib phase, hasAuth⟩ dir app = [] := by
  apply Socks.hstep_no_early_egress
  cases phase <;> simp [toLib]

/-! ## (3) The tunnel opens only when the real handshake reaches `established` -/

/-- The real handshake emits `tunnelUp` only on the transition *into* `established`. -/
theorem hstep_tunnelUp_established {s : Socks.HState} {buf : List UInt8}
    (h : (Socks.hstep s buf).2 = Socks.Out.tunnelUp) :
    (Socks.hstep s buf).1.phase = Socks.Phase.established := by
  obtain ⟨ph, ha⟩ := s
  cases ph with
  | established => simp [Socks.hstep] at h
  | failed => simp [Socks.hstep] at h
  | awaitGreeting =>
    simp only [Socks.hstep] at h ⊢
    cases hp : Socks.parseMethod buf with
    | incomplete => simp_all
    | error => simp_all
    | complete m c =>
      by_cases hm0 : m = 0x00
      · simp_all
      · by_cases hm2 : m = 0x02
        · by_cases hca : ha = true <;> simp_all
        · simp_all
  | awaitAuth =>
    simp only [Socks.hstep] at h ⊢
    cases hp : Socks.parseAuthStatus buf with
    | incomplete => simp_all
    | error => simp_all
    | complete ok c =>
      by_cases hok : ok = true <;> simp_all
  | awaitReply =>
    simp only [Socks.hstep] at h ⊢
    cases hp : Socks.parseReply buf with
    | incomplete => simp_all
    | error => simp_all
    | complete code c =>
      by_cases hc0 : code = 0x00
      · subst hc0; rfl
      · simp_all

/-- The wired adapter yields `.connect` only when the real `Socks.hstep` emits `tunnelUp`. -/
theorem connect_implies_tunnelUp (target : Addr) (hasAuth : Bool)
    (phase : SocksPhase) (buf : List UInt8) (addr : Addr) (c : Nat)
    (h : socksFeedReal target hasAuth phase buf = .connect addr c) :
    (Socks.hstep ⟨toLib phase, hasAuth⟩ buf).2 = Socks.Out.tunnelUp := by
  unfold socksFeedReal at h
  split at h <;> simp_all

/-- **The FSM tunnel opens only at `established`.** The wired `socksFeed` produces
`.connect addr c` — the sole trigger for `connectUpstream` and thence `plainTunnel` — only
when the real `Socks.hstep` has reached the `established` phase. There is no earlier door
to the relay. -/
theorem socks_connect_reaches_established (target : Addr) (hasAuth : Bool)
    (phase : SocksPhase) (buf : List UInt8) (addr : Addr) (c : Nat)
    (h : socksFeedReal target hasAuth phase buf = .connect addr c) :
    (Socks.hstep ⟨toLib phase, hasAuth⟩ buf).1.phase = Socks.Phase.established :=
  hstep_tunnelUp_established (connect_implies_tunnelUp target hasAuth phase buf addr c h)

/-! ## The seam theorem -/

/-- **SOCKS no-early-egress seam.** For a `wireSocks`-wired config, composing the FSM relay
gating with the real `Socks` handshake's no-early-egress:

1. no application byte is relayed upstream while the FSM is in `socksHandshake`
   (`socksFeed_no_upstream`);
2. the real `Socks` relay gate is closed for every handshake phase
   (`socks_relay_gate_closed`, from the library's `hstep_no_early_egress`);
3. the FSM opens the tunnel (`.connect` → `connectUpstream` → `plainTunnel`) only when the
   real handshake reaches `established` (`socks_connect_reaches_established`).

Together: no application bytes are relayed before the real SOCKS handshake reaches
`established`. -/
theorem socks_no_early_egress_seam (target : Addr) (hasAuth : Bool) (cfg : Config)
    (buf : List UInt8) (phase : SocksPhase) (data : List UInt8) :
    (∀ o ∈ (onBytes (wireSocks target hasAuth cfg)
        (.socksHandshake buf phase) data).outs, isUpstream o = false)
    ∧ (∀ (dir : Socks.Dir) (app : List UInt8),
        Socks.hEgress ⟨toLib phase, hasAuth⟩ dir app = [])
    ∧ (∀ (addr : Addr) (c : Nat),
        (wireSocks target hasAuth cfg).socksFeed phase buf = .connect addr c →
          (Socks.hstep ⟨toLib phase, hasAuth⟩ buf).1.phase = Socks.Phase.established) := by
  refine ⟨?_, ?_, ?_⟩
  · exact socksFeed_no_upstream _ _ _ _
  · intro dir app; exact socks_relay_gate_closed _ _ _ _
  · intro addr c h
    exact socks_connect_reaches_established target hasAuth phase buf addr c h

/-- The seam, specialized to the concrete `demoSocksConfig`. -/
theorem demoSocksConfig_no_early_egress_seam
    (buf : List UInt8) (phase : SocksPhase) (data : List UInt8) :
    (∀ o ∈ (onBytes demoSocksConfig (.socksHandshake buf phase) data).outs,
        isUpstream o = false)
    ∧ (∀ (dir : Socks.Dir) (app : List UInt8),
        Socks.hEgress ⟨toLib phase, false⟩ dir app = [])
    ∧ (∀ (addr : Addr) (c : Nat),
        demoSocksConfig.socksFeed phase buf = .connect addr c →
          (Socks.hstep ⟨toLib phase, false⟩ buf).1.phase = Socks.Phase.established) :=
  socks_no_early_egress_seam ⟨0⟩ false Reactor.Config.demoConfig buf phase data

end Reactor
