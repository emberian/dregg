import Reactor.Bridge
import Reactor.QuicIngress

/-!
# Reactor.WireH3 — the H3 frame + QPACK-decode Wf-preservation, landed on the
deployed QUIC serve entry

`H3` proved two core facts about parsing an HTTP/3 request off the wire:

* **frame decode** (`H3.decFrame` / `decFrame_consumed`) — the tri-state frame
  decoder is total and consumed-monotone (a completed frame eats `1 ≤ n ≤ len`
  bytes, the operational form that makes the frame loop terminate), and
* **QPACK-decode Wf-preservation** (`H3.Qpack.decodeFieldSection_wf`, the H3
  analogue of the H1 parser's `Wf` discharge) — decoding a HEADERS field section
  *into* the arena store yields a **well-formed** store: every emitted view entry
  is in-bounds of the arena it addresses, for every Huffman-decoder behaviour and
  every input.

Those are island facts about the codec in isolation. The deployed QUIC path is
`Reactor.QuicIngress.datagramServe` — the QUIC sibling of
`Reactor.Ingress.deployStepIngress`, the serve entry an orchestrator hangs a UDP
socket driver off (recv a datagram, call `datagramServe`, feed the emitted
`RingSubmission.dispatch` into the **same guarded serve** the TCP lane runs,
`Reactor.Deploy.serveGuarded`). It runs the REAL engines — `Quic.step` delivers,
`H3.decFrame` yields the frame, `H3.Qpack.decodeFieldSection` writes the field
section into the lane's live arena, which is then carried forward as the advanced
lane state.

This file transports the QPACK Wf-preservation onto that running store. `Reactor.
QuicIngress.quic_ingress_dispatch` already established *which* submission the
datagram serve emits (exactly the dispatch of the decoded request), but it left
the **shape of the advanced arena** unstated. `h3_deployed` closes that: on a
well-formed H3 HEADERS datagram into an established connection the deployed
datagram serve

* advances its lane store to one that is still **`Wf`** — the store the *next*
  datagram decodes into is well-formed, so the QPACK invariant is preserved
  across the running loop, not just for one section in a scratch store — and
* emits **exactly** the `dispatch` of the decoded request, the one that feeds
  `serveGuarded`.

The `Wf` conclusion is `H3.Qpack.decodeFieldSection_wf` carried onto the store the
deployed serve actually keeps; the dispatch conclusion is `quic_ingress_dispatch`.
Neither is a restatement: the Wf fact was never before stated of `datagramServe`'s
output store.

(`Reactor.Bridge` is imported for the deployed-path pattern context; the H3 codec
runs on the QUIC datagram lane, not the plainH1 `deploySubs` recv path the Bridge
lift equates, so the transport here anchors on the QUIC serve entry directly — the
same posture `Reactor.WireMore` takes for the island libraries that key on
deployed values rather than on `reactorSubs`.)
-/

namespace Reactor
namespace WireH3

open Proto (Bytes)
open Reactor.Quic (QuicState QuicConfig)
open Reactor.QuicIngress (datagramServe requestOfHeaders)

/-- **`h3_deployed` — the H3 frame + QPACK-decode Wf-preservation, on the deployed
QUIC serve entry.** A datagram in the app-data space, into an `established` QUIC
connection, carrying a stream whose head `H3.decFrame` completes to a HEADERS
frame (`hframe`) whose QPACK field section decodes to `d` (`hqpack`), fed into the
deployed datagram serve `Reactor.QuicIngress.datagramServe` (which runs the REAL
`Quic.step` + `H3.decFrame` + `H3.Qpack.decodeFieldSection`), yields:

* an advanced lane state whose arena store is **well-formed** — the QPACK
  Wf-preservation (`H3.Qpack.decodeFieldSection_wf`) transported onto the store
  the running serve carries forward, so the next datagram decodes into a `Wf`
  store; and
* **exactly** the `RingSubmission.dispatch` of the decoded request
  (`requestOfHeaders d.store d.pseudo d.fields`) — the submission the deployed
  `serveGuarded` consumes (`quic_ingress_dispatch`).

The `Wf` half is the H3 library's headline theorem landed on the deployed path;
the dispatch half anchors that store to the request that actually enters the
serve. -/
theorem h3_deployed (cfg : QuicConfig) (st : QuicState)
    (pn sid consumed : Nat) (h3 encoded : Bytes) (d : _root_.H3.Qpack.Decoded)
    (hest : st.conn.phase = .established)
    (hframe : _root_.H3.decFrame h3 = .complete (.headers encoded) consumed)
    (hqpack : _root_.H3.Qpack.decodeFieldSection cfg.huffman st.store encoded = .ok d)
    (hwf : st.store.Wf) :
    (datagramServe cfg st (.recvDatagram .appData pn (.stream sid h3))).1.store.Wf
    ∧ (datagramServe cfg st (.recvDatagram .appData pn (.stream sid h3))).2
        = [RingSubmission.dispatch (requestOfHeaders d.store d.pseudo d.fields)] := by
  have hstep := Reactor.QuicIngress.quic_ingress_dispatch cfg st pn sid consumed
    h3 encoded d hest hframe hqpack hwf
  refine ⟨?_, ?_⟩
  · rw [hstep]
    exact _root_.H3.Qpack.decodeFieldSection_wf cfg.huffman st.store encoded d hwf hqpack
  · rw [hstep]

/-! ## Axiom audit — closed on the standard axioms only -/

#print axioms h3_deployed

end WireH3
end Reactor
