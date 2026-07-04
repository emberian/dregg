import Reactor.Bridge
import Mux

/-!
# Reactor.WireMux — the H2 stream-mux + RFC 9218 scheduler on the DEPLOYED serve path

`Mux` proves two core facts about HTTP/2 stream multiplexing:

* **RFC 9218 priority ordering** (`Mux.Scheduler`): `select` picks the pending
  stream of minimal rank — urgency first (lower = higher priority), then
  non-incremental before incremental, id as tie-break. `select_min_urgency` /
  `select_priority_respected` say the picked stream has minimal urgency among the
  pending set: no strictly-higher-urgency pending stream is ever passed over.
* **Byte conservation of the mux** (`Mux.Conservation`): however many streams'
  chunks are interleaved onto one tagged wire, de-interleaving by stream id
  (`demux ∘ wireOf`) recovers each stream's in-order payload exactly —
  `demux_wireOf` — with no byte lost, duplicated, reordered, or cross-contaminated
  between streams.

These were proved as an island. This file lands them on the bytes the deployed
binary actually emits. The value the deployed orb serializes is
`Reactor.Deploy.deployResp input` (its `.body` is the emitted response body); via
`Reactor.Bridge.deploySubs_eq_reactorSubs` that response is computed from the *same*
reactor the island lanes were proved over (`deployResp` is built on `deploySubs`,
which the Bridge equates to `reactorSubs`). Modeling the deployed response as the
send queue of its H2 stream (id 1, the first client-opened stream, default RFC 9218
priority), the two Mux theorems transport onto the deployed served body:

* `mux_min_urgency_deployed` / `mux_priority_deployed` — when the mux picks the
  deployed response's stream to serve, it never skipped a higher-urgency pending
  stream (priority respected on the deployed serve).
* `mux_conserves_deployed` / `mux_no_corruption_deployed` / `mux_demux_deployed` —
  the deployed body round-trips through the mux, and a concurrent stream on the
  same wire does not corrupt it.

Honest scope (same posture as `Reactor.WireMore`): these are proof-attachment
seams. They state Mux's real, meaning-constraining theorems about the actual
deployed served body / its scheduled stream, discharged by Mux's own proofs — not
a runtime scheduler wired into the event loop. What they establish is that the H2
mux + priority guarantees *hold of the bytes the deployed path carries*.
-/

namespace Reactor
namespace WireMux

open Proto (Bytes)

/-! ## The Bridge anchor — the deployed response is a value of the shared reactor -/

/-- The deployed reactor's submissions are exactly the test reactor's, on the
plainH1 recv path (`Bridge.deploySubs_eq_reactorSubs`). `deployResp` is built on
`deploySubs`, so the response the Mux seams below range over is a function of the
same `reactorSubs` the island lanes proved their seams about — not a side model. -/
theorem deployed_subs_agree (input : Bytes) :
    Reactor.Deploy.deploySubs input = Reactor.reactorSubs input :=
  Reactor.Bridge.deploySubs_eq_reactorSubs input

/-! ## The deployed response as its H2 stream

The deployed response body is what the server sends on the stream the client
opened. Model it as a `Mux.Stream`: stream id 1 (the first client-opened H2
stream), the RFC 9218 default priority, and the deployed body as its pending send
queue. -/

/-- The H2 stream id carrying the deployed response (first client-opened stream). -/
def deploySid : Mux.StreamId := 1

/-- The deployed response modeled as its schedulable H2 stream: id `deploySid`,
default RFC 9218 priority, the deployed served body as the pending send queue. -/
def deployStream (input : Bytes) : Mux.Stream :=
  { id    := deploySid
    prio  := Mux.Priority.default
    queue := (Reactor.Deploy.deployResp input).body }

/-! ## (1) RFC 9218 priority — the deployed stream is served in priority order -/

/-- **`mux_min_urgency_deployed` — priority respected on the deployed serve.**
When the mux scheduler picks the deployed response's stream out of a set of
concurrent streams, that stream has minimal urgency among all pending streams:
the deployed response is never served ahead of a strictly-higher-priority one.
(`Mux.select_min_urgency` transported onto `deployStream input`.) -/
theorem mux_min_urgency_deployed (input : Bytes) (streams : List Mux.Stream)
    (hsel : Mux.select streams = some (deployStream input)) :
    ∀ t ∈ streams, t.hasPending = true →
      (deployStream input).prio.urgency ≤ t.prio.urgency :=
  Mux.select_min_urgency hsel

/-- **`mux_priority_deployed` — no higher-urgency stream is passed over.** If, when
the deployed response's stream is the one selected, some other pending stream `t`
had strictly higher urgency (lower urgency value), that is impossible: the mux
would have served `t` first. The direct "served before" form of RFC 9218 priority
on the deployed serve. (`Mux.select_priority_respected`.) -/
theorem mux_priority_deployed (input : Bytes) (streams : List Mux.Stream)
    (t : Mux.Stream)
    (hsel : Mux.select streams = some (deployStream input))
    (ht : t ∈ streams) (hp : t.hasPending = true)
    (hu : t.prio.urgency < (deployStream input).prio.urgency) : False :=
  Mux.select_priority_respected hsel ht hp hu

/-! ## (2) H2 stream-mux — the deployed body is conserved on the wire -/

/-- **`mux_demux_deployed` — general conservation over the deployed stream.**
However the deployed response's chunks are interleaved with any other streams'
chunks on one tagged wire, de-interleaving by the deployed stream id recovers
exactly that stream's in-order payload — `Mux.Conservation.demux_wireOf` on the
deployed stream id. -/
theorem mux_demux_deployed (sends : List (Mux.StreamId × List UInt8)) :
    Mux.Conservation.demux (Mux.Conservation.wireOf sends) deploySid
      = Mux.Conservation.payloadOf sends deploySid :=
  Mux.Conservation.demux_wireOf sends deploySid

/-- **`mux_conserves_deployed` — the deployed body round-trips through the mux.**
Laying the deployed response body onto the wire as its stream's single chunk and
de-interleaving by the deployed stream id returns exactly the deployed body: no
byte lost, duplicated, or reordered. -/
theorem mux_conserves_deployed (input : Bytes) :
    Mux.Conservation.demux
        (Mux.Conservation.wireOf [(deploySid, (Reactor.Deploy.deployResp input).body)])
        deploySid
      = (Reactor.Deploy.deployResp input).body := by
  rw [Mux.Conservation.demux_wireOf]
  simp [Mux.Conservation.payloadOf, deploySid]

/-- **`mux_no_corruption_deployed` — a concurrent stream does not corrupt the
deployed body.** Interleaving any other stream `sid ≠ deploySid` ahead of the
deployed response on the same mux wire leaves the deployed body's reconstruction
untouched: de-interleaving still returns exactly the deployed body. This is the H2
stream isolation guarantee on the deployed served bytes. (`demux_other_noop`.) -/
theorem mux_no_corruption_deployed (input : Bytes)
    (sid : Mux.StreamId) (bs : List UInt8) (h : sid ≠ deploySid) :
    Mux.Conservation.demux
        (Mux.Conservation.wireOf
          ((sid, bs) :: [(deploySid, (Reactor.Deploy.deployResp input).body)]))
        deploySid
      = (Reactor.Deploy.deployResp input).body := by
  rw [Mux.Conservation.demux_other_noop sid bs _ deploySid h,
      Mux.Conservation.demux_wireOf]
  simp [Mux.Conservation.payloadOf, deploySid]

/-! ## Axiom audit — every deployed Mux seam closes on the standard axioms only -/

#print axioms deployed_subs_agree
#print axioms mux_min_urgency_deployed
#print axioms mux_priority_deployed
#print axioms mux_demux_deployed
#print axioms mux_conserves_deployed
#print axioms mux_no_corruption_deployed

end WireMux
end Reactor
