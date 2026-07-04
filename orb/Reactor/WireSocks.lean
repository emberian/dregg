import Reactor.Bridge
import Reactor.Deploy
import Reactor.Socks

/-!
# Reactor.WireSocks — the SOCKS egress gate, landed on the DEPLOYED config

`Reactor.Socks` proved the SOCKS no-early-egress seam
(`socks_no_early_egress_seam`) for *any* config wired with the real handshake
engine: driving the real `Socks.hstep` through the `socksFeed` field, no
application byte reaches the upstream socket before the handshake reaches
`established`. The load-bearing library fact is `Socks.hstep_no_early_egress`
(the phase-gated relay `hEgress` forwards nothing off any non-`established`
phase).

That seam was stated over an arbitrary `cfg`. This file instantiates it at the
one config the deployed binary actually runs: `Reactor.Deploy.deployConfig`,
which is `demoConfig` with the three codec lanes replaced by their real engines
—

    deployConfig = wireSocks ⟨0⟩ false (Ws.wireWs (TlsWire.wireTls TlsWire.demoTlsCfg demoConfig))

and which `serveFull` / `serveGuarded` / `deployStep` (what `Arena.Orb.main`
runs) step over. `deployConfig` is definitionally `wireSocks ⟨0⟩ false _`, so the
seam applies to it verbatim: the SOCKS egress property is transported onto the
deployed path, not restated.

`deployed_socksFeed_real` records that the `socksFeed` the deployed config reads
is the real `Socks.hstep` adapter (via `Reactor.Deploy.deploy_uses_real_socks`),
not the inert `.fail` stub — so `socks_deployed` is a fact about the real engine
on the real config, not a vacuous one about a stub.
-/

namespace Reactor.WireSocks

open Proto (SocksPhase Addr onBytes)

/-- The base config the SOCKS lane wires over inside `deployConfig` (the TLS +
WebSocket real-engine config). `deployConfig = wireSocks ⟨0⟩ false deployBase`. -/
private def deployBase : Proto.Config :=
  Ws.wireWs (TlsWire.wireTls TlsWire.demoTlsCfg Reactor.Config.demoConfig)

/-- The deployed config's `socksFeed` is the real `Socks.hstep` adapter — not the
`.fail` stub `demoConfig` carried. So the gate below is about the real engine. -/
theorem deployed_socksFeed_real :
    Reactor.Deploy.deployConfig.socksFeed = Reactor.socksFeedReal ⟨0⟩ false :=
  Reactor.Deploy.deploy_uses_real_socks

/-- **`socks_deployed` — the SOCKS no-early-egress gate, on the config `main`
runs.** For the deployed config (`deployConfig`, over which `serveFull` /
`serveGuarded` / `deployStep` step), composing the FSM structural gate with the
real `Socks` handshake's proven `hstep_no_early_egress`:

1. while the FSM is in `socksHandshake`, `onBytes` over `deployConfig` emits no
   `sendUpstream` output — no application byte is relayed upstream mid-handshake;
2. the real `Socks` relay gate `hEgress` forwards nothing for every phase that
   keeps the FSM handshaking (none map to `established`);
3. the wired `socksFeed` opens the tunnel (`.connect` → `connectUpstream` →
   `plainTunnel`, the only door to the relay) *only* when the real `Socks.hstep`
   reaches `established`.

Together: on the deployed path, no application bytes reach the upstream socket
before the real SOCKS handshake establishes. This is
`socks_no_early_egress_seam` instantiated at `deployConfig` (definitionally
`wireSocks ⟨0⟩ false deployBase`). -/
theorem socks_deployed (buf : List UInt8) (phase : SocksPhase) (data : List UInt8) :
    (∀ o ∈ (onBytes Reactor.Deploy.deployConfig (.socksHandshake buf phase) data).outs,
        Reactor.isUpstream o = false)
    ∧ (∀ (dir : Socks.Dir) (app : List UInt8),
        Socks.hEgress ⟨Reactor.toLib phase, false⟩ dir app = [])
    ∧ (∀ (addr : Addr) (c : Nat),
        Reactor.Deploy.deployConfig.socksFeed phase buf = .connect addr c →
          (Socks.hstep ⟨Reactor.toLib phase, false⟩ buf).1.phase
            = Socks.Phase.established) :=
  Reactor.socks_no_early_egress_seam ⟨0⟩ false deployBase buf phase data

end Reactor.WireSocks
