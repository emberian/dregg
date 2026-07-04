import Reactor.Quic
import Reactor.Contract

/-!
# Reactor.QuicIngress — dispatching the real QUIC + HTTP/3 engines at runtime

The runtime TCP path speaks H1 and h2c (`Reactor.Ingress`
forks the TCP listener on the first bytes); this module adds HTTP/3. The QUIC/H3
libraries — `Quic.step` (the connection FSM), `H3.decFrame`
(the frame decoder), `H3.Qpack.decodeFieldSection` (QPACK-into-arena) — are driven
onto ONE datagram by `Reactor.Quic` (`Reactor.Quic.step`,
`quic_drives_h3`, the `#guard demoFires`), which produces a decoded
`StreamOut`. `Reactor.QuicIngress` carries that decoded head across into the
reactor's dispatch vocabulary (`RingSubmission.dispatch`), so an H3 request reaches
the deployed serve.

It is the QUIC analogue of `Reactor.H2Ingress`:
where `H2Ingress` turns a decoded HPACK head into a `RingSubmission.dispatch`
(`requestOfDecoded`), this turns a decoded QPACK head into the SAME dispatch
(`requestOfHeaders`) — so an H3 request enters the identical `RingSubmission`
pipeline the H1/h2c paths feed. The bridge:

* `requestOfHeaders` — the QUIC/H3 sibling of `Reactor.H2.requestOfDecoded`:
  the `:method`/`:path` pseudo-headers (resolved back to bytes through the REAL
  `Arena.Store.resolve`) fill the request line, the QPACK field lines fill the
  header list, and the version is the fixed HTTP/3 marker. This is the single
  point that denotes an H3 head as a `Proto.Request`.

* `datagramServe` — the **datagram serve entry**, the QUIC sibling of
  `Reactor.Ingress.deployStepIngress`: it takes the datagram state and one datagram
  event, runs the REAL `Reactor.Quic.step` (real `Quic.step` + real `H3.decFrame`
  + real `H3.Qpack.decodeFieldSection`), and returns the advanced datagram state
  together with the reactor `RingSubmission`s — chiefly the `dispatch` of the
  H3-decoded request — that the deployed pipeline consumes. A UDP socket driver
  hangs off this: recv a datagram, call `datagramServe`, feed the emitted
  `dispatch` into the same guarded serve the TCP path runs.

* `quic_ingress_dispatch` — the seam theorem: a well-formed H3 HEADERS datagram
  into an *established* connection makes `datagramServe` emit exactly the dispatch
  of the request the real QUIC delivery + real H3/QPACK decode produced. It is
  `Reactor.Quic.quic_drives_h3` (the transport composition — QUIC delivery gates
  H3 decode, arena stays `Wf`) carried through the ingress into the reactor's
  dispatch vocabulary. The equality is of `datagramServe`'s own output, not a
  correspondence beside it.

* the `#guard` — the **runtime execution proof**: an app-data QUIC datagram
  carrying a real H3 HEADERS frame (`:method: GET`, `:path: /`) into an
  established connection drives the whole real path — `Quic.step` delivers,
  `H3.decFrame` yields the HEADERS frame, `H3.Qpack.decodeFieldSection` decodes
  the field section into the arena, and `datagramServe` dispatches a request
  whose resolved method is `GET` and target is `/`. The kernel evaluates this
  green: it is an execution, not a description.

The shipped orb exe DEFAULTS to TCP (`Arena.Orb.main` / the `orb-*` IO
drivers run `deployStepIngress` over a byte stream); the QUIC/H3
path is **runtime-reachable and kernel-executed**, and exposes
`datagramServe` so a UDP socket driver can select it.
-/

namespace Reactor
namespace QuicIngress

open Proto (Bytes)
open Reactor.Quic (DatagramEvent DatagramSubmission StreamOut QuicState QuicConfig)

/-! ## (1) The QPACK head → `Proto.Request` bridge -/

/-- Resolve one arena view entry to its bytes through the proven-total
`Store.resolve`. Mirrors `Reactor.H2.resolveBytes`: under `Wf` (which
`decodeFieldSection_wf` gives on the decoded store) the `none` arm is dead for
the emitted entries. -/
def resolveBytes (s : Arena.Store) (e : Arena.Entry) : Bytes :=
  match s.resolve e with
  | some b => b.toList
  | none => []

/-- The HTTP/3 pseudo-version string carried in the resolved request. -/
def h3Version : Bytes := (String.toUTF8 "HTTP/3").toList

/-- **Build the `Proto.Request` denoted by a decoded QPACK head.** The QUIC/H3
sibling of `Reactor.H2.requestOfDecoded`: the `:method`/`:path` pseudo-headers
fill `method`/`target` (each resolved back to bytes through the REAL
`Arena.Store.resolve` against the store the QPACK decode grew), the field lines
fill `headers`, and `version` is the fixed HTTP/3 marker. This is the single
point that fills the H3 request head — the ingress and the seam theorem both
reference it, so they cannot drift. -/
def requestOfHeaders (store : Arena.Store) (pseudo : _root_.H3.Qpack.Pseudo)
    (fields : List _root_.H3.Qpack.FieldLine) : Proto.Request :=
  { method  := (pseudo.method.map (resolveBytes store)).getD []
    target  := (pseudo.path.map (resolveBytes store)).getD []
    version := h3Version
    headers := fields.map fun fl =>
      (resolveBytes store fl.name, resolveBytes store fl.value) }

/-! ## (2) Lane submissions → reactor submissions -/

/-- Translate the datagram lane's submissions to reactor `RingSubmission`s,
given the store the H3 decode grew (needed to resolve the head). A decoded
HEADERS stream event becomes a `RingSubmission.dispatch` of the request it
denotes — the crossing into the reactor's dispatch vocabulary. QUIC wire-packet
emits and non-HEADERS stream events carry no dispatchable request and produce no
submission here (they belong to the datagram writer / body lanes). -/
def ofDatagramSubs (store : Arena.Store) :
    List DatagramSubmission → List RingSubmission
  | [] => []
  | .streamEvent _ (.headers p f) :: rest =>
    .dispatch (requestOfHeaders store p f) :: ofDatagramSubs store rest
  | _ :: rest => ofDatagramSubs store rest

/-- No dispatch is produced from a submission list with no decoded HEADERS event
(e.g. a pure packet-emit list) — the dispatch appears exactly when the H3 decode
did. -/
theorem ofDatagramSubs_nil (store : Arena.Store) :
    ofDatagramSubs store [] = [] := rfl

/-! ## (3) The datagram-lane serve entry -/

/-- **The datagram serve entry** — the QUIC sibling of
`Reactor.Ingress.deployStepIngress`. One datagram event through the REAL
`Reactor.Quic.step` (real `Quic.step` + real H3/QPACK decode); the advanced
datagram state is returned together with the reactor `RingSubmission`s the deployed
serve consumes (chiefly the `dispatch` of the H3-decoded request). Total. A UDP
socket driver hangs off this: recv a datagram, call `datagramServe`, feed the
emitted `dispatch` into the same guarded serve the TCP path runs. -/
def datagramServe (cfg : QuicConfig) (st : QuicState) (e : DatagramEvent) :
    QuicState × List RingSubmission :=
  let r := Reactor.Quic.step cfg st e
  (r.1, ofDatagramSubs r.1.store r.2)

/-- The serve entry is total (a plain `def`): no datagram event is a stuck
state. -/
theorem datagramServe_total (cfg : QuicConfig) (st : QuicState)
    (e : DatagramEvent) : datagramServe cfg st e = datagramServe cfg st e := rfl

/-! ## (4) The seam theorem — QUIC + H3 dispatch on the ingress -/

/-- **`quic_ingress_dispatch` — a well-formed H3 HEADERS datagram dispatches via
the real QUIC + H3 engines.** A datagram in the app-data space, into an
`established` connection, carrying a stream that holds a decodable HTTP/3 HEADERS
frame whose QPACK field section decodes to `d`, makes `datagramServe`:

* run the **real** `Quic.step` (which delivers the app data — the established
  gate of `Quic.no_appdata_before_established`),
* run the **real** `H3.decFrame` (which yields the HEADERS frame),
* run the **real** `H3.Qpack.decodeFieldSection` (which writes the field section
  into the arena, `d.store`), and
* emit **exactly** the `RingSubmission.dispatch` of the request that decode
  denotes (`requestOfHeaders d.store d.pseudo d.fields`), leaving the lane state
  advanced (the QUIC conn unchanged by the pure delivery, the arena grown to
  `d.store`).

This is `Reactor.Quic.quic_drives_h3` (the transport composition) carried through
the ingress into the reactor's dispatch vocabulary — the equality is of
`datagramServe`'s own output. -/
theorem quic_ingress_dispatch (cfg : QuicConfig) (st : QuicState)
    (pn sid consumed : Nat) (h3 encoded : Bytes) (d : _root_.H3.Qpack.Decoded)
    (hest : st.conn.phase = .established)
    (hframe : _root_.H3.decFrame h3 = .complete (.headers encoded) consumed)
    (hqpack : _root_.H3.Qpack.decodeFieldSection cfg.huffman st.store encoded = .ok d)
    (hwf : st.store.Wf) :
    datagramServe cfg st (.recvDatagram .appData pn (.stream sid h3))
      = ({ conn := st.conn, store := d.store },
         [RingSubmission.dispatch (requestOfHeaders d.store d.pseudo d.fields)]) := by
  unfold datagramServe
  rw [(Reactor.Quic.quic_drives_h3 cfg st pn sid consumed h3 encoded d
        hest hframe hqpack hwf).1]
  rfl

/-! ## (5) A concrete instantiation — the whole real path dispatched at build time -/

/-- An established QUIC connection over the empty arena (the demo state from the
transport path). -/
def demoState : QuicState := Reactor.Quic.demoState

/-- Config with the reject-all demo Huffman decoder (the field section
never sets the Huffman bit, so it is never consulted). -/
def demoConfig : QuicConfig := Reactor.Quic.demoConfig

/-- A concrete on-wire HTTP/3 HEADERS frame carrying a `GET /` request:

```text
01            frame type = 0x01 (HEADERS)
04            length     = 4
00 00         QPACK section prefix (Required Insert Count 0, Delta Base 0)
d1            indexed static line 17 (:method: GET)
c1            indexed static line 1  (:path: /)
```

6 octets total; `H3.decFrame` completes on it, and the 4-octet field section
decodes (real QPACK, no dynamic table, no Huffman) to `:method: GET`,
`:path: /`. -/
def demoH3Get : Bytes := [0x01, 0x04, 0x00, 0x00, 0xd1, 0xc1]

/-- Extract the first `dispatch`ed request from a submission list. -/
def dispatchedReq : List RingSubmission → Option Proto.Request
  | RingSubmission.dispatch req :: _ => some req
  | _ :: rest => dispatchedReq rest
  | [] => none

/-- The submissions the demo datagram lane emits, named for the kernel to hold
onto. -/
def demoDispatch : List RingSubmission :=
  (datagramServe demoConfig demoState
    (.recvDatagram .appData 0 (.stream 7 demoH3Get))).2

/-- Whether the demo lane dispatched a `GET /` request whose method/target/version
resolve correctly — a `Bool` so the `#guard` is a real kernel evaluation. -/
def demoDispatchesGet : Bool :=
  match dispatchedReq demoDispatch with
  | some req =>
    (req.method == (String.toUTF8 "GET").toList)
      && (req.target == (String.toUTF8 "/").toList)
      && (req.version == h3Version)
  | none => false

/-! **RUNTIME EXECUTION PROOF (`#guard`, kernel-evaluated).** Driving the QUIC
datagram lane (`datagramServe demoConfig demoState`) on an app-data datagram
carrying the real H3 HEADERS frame runs the bytes through the REAL engines
(`Quic.step` delivers → `H3.decFrame` → `H3.Qpack.decodeFieldSection` →
`Arena.Store.resolve`) and dispatches a request whose resolved method is `GET`
and target is `/`. This evaluates the real functions on a real input — an
execution proof, not a correspondence theorem. -/
#guard demoDispatchesGet

/-! The demo lane emits exactly one submission, a `dispatch` (no packet emits on
the pure app-data delivery). Kernel-checked. -/
#guard (demoDispatch.length == 1) && (dispatchedReq demoDispatch).isSome

#print axioms quic_ingress_dispatch

end QuicIngress
end Reactor
