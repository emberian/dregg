import Reactor.Deploy
import Reactor.H2Ingress

/-!
# Reactor.Ingress — one listener, both protocols (HTTP/1.1 and h2c prior-knowledge)

The shipped orb `main` used to drive a single `plainH1` connection: it served
HTTP/1.1 and nothing else. The H2 engine was installed in `deployConfig`
(`deploy_h2_real`) and even proven runtime-reachable (`H2Ingress.h2c_runtime_dispatch`),
but `main` never *entered* it — the binary spoke one protocol.

This file is the front door that speaks both. It inspects the first bytes of a
connection and selects the initial `Proto.Conn` before a single frame is parsed:

* if the bytes begin with the HTTP/2 connection preface
  (`PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`, RFC 9113 §3.4) — the h2c prior-knowledge
  handshake — the connection starts in `.plainH2` (`H2Ingress.mkH2c`, the real
  H2 engine) and the post-preface bytes are fed straight into it;
* otherwise the connection starts in `.plainH1` (`Proto.Conn.mkPlain`) and is
  served by the existing guarded HTTP/1.1 path, byte-for-byte unchanged.

Both branches run the SAME proven reactor over the SAME `deployConfig` — only the
initial `Proto.Conn` differs. `serveIngress` is the response function; on the H1
branch it is *definitionally* `Reactor.Deploy.serveGuarded` (so every guarded seam
— Policy 403, traversal 404, the 200 with `x-upstream`/`x-corr` — carries over
untouched), and on the H2 branch it drives the request the REAL `h2FeedFn` decoded
from the frame through the same serve.

`deployStepIngress` is the observed step `main` now runs (`serveIngress` plus the
REAL `Metrics`/`Tap`/`Trace` advance, identical to `deployStepGuarded`).

The seam theorem `ingress_selects_protocol` states the fork over the bytes `main`
reads: a preface-led input is served by the `.plainH2` (real `h2Feed`) path and
dispatches the HPACK-decoded request; a non-preface input is served by the
`.plainH1` guarded path, byte-identical to `serveGuarded`.
-/

namespace Reactor
namespace Ingress

open Proto (Bytes)

/-! ## (1) The HTTP/2 connection preface -/

/-- The 24-octet HTTP/2 connection preface, `PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`
(RFC 9113 §3.4). A client speaking h2c with prior knowledge sends exactly these
bytes before its first frame; no HTTP/1.1 request line can begin with them
(`PRI` is not a registered method and the `* HTTP/2.0` target/version pair is
unique), so it is an unambiguous discriminator. -/
def h2Preface : Bytes :=
  [ 0x50, 0x52, 0x49, 0x20, 0x2a, 0x20, 0x48, 0x54, 0x54, 0x50, 0x2f, 0x32,
    0x2e, 0x30, 0x0d, 0x0a, 0x0d, 0x0a, 0x53, 0x4d, 0x0d, 0x0a, 0x0d, 0x0a ]

/-- The preface is 24 octets. -/
theorem h2Preface_length : h2Preface.length = 24 := rfl

/-- Does an input begin with the HTTP/2 preface? Exact-prefix test on the first
octets — the h2c prior-knowledge discriminator. -/
def hasH2Preface (input : Bytes) : Bool := List.isPrefixOf h2Preface input

/-- Anything of the form `preface ++ rest` is recognized as h2c. -/
theorem hasH2Preface_append (bs : Bytes) : hasH2Preface (h2Preface ++ bs) = true := by
  unfold hasH2Preface
  rw [List.isPrefixOf_iff_prefix]
  exact List.prefix_append h2Preface bs

/-! ## (2) Protocol selection: the initial Conn and the bytes fed to it -/

/-- **The selected initial connection.** Preface ⇒ the real h2c engine parked in
`.plainH2` (`H2Ingress.mkH2c`); otherwise the plain HTTP/1.1 listener connection
(`Proto.Conn.mkPlain`). This is the whole fork — one `Proto.Conn` or the other,
chosen from the first bytes. -/
def ingressConn (input : Bytes) : Proto.Conn :=
  cond (hasH2Preface input) Reactor.H2Ingress.mkH2c Proto.Conn.mkPlain

/-- **The bytes handed to the selected engine.** For h2c, the preface is consumed
by the discriminator and the post-preface bytes (the first real frame onward) are
fed to the H2 engine; for HTTP/1.1, the whole input is the request. -/
def ingressFeed (input : Bytes) : Bytes :=
  cond (hasH2Preface input) (input.drop h2Preface.length) input

/-- On a non-preface input the connection is the plain HTTP/1.1 listener. -/
theorem ingressConn_h1 (input : Bytes) (h : hasH2Preface input = false) :
    ingressConn input = Proto.Conn.mkPlain := by
  unfold ingressConn; rw [h]; rfl

/-- On a non-preface input the whole input is the request bytes. -/
theorem ingressFeed_h1 (input : Bytes) (h : hasH2Preface input = false) :
    ingressFeed input = input := by
  unfold ingressFeed; rw [h]; rfl

/-- On a preface-led input the connection is the real h2c engine (`mkH2c`). -/
theorem ingressConn_h2 (bs : Bytes) :
    ingressConn (h2Preface ++ bs) = Reactor.H2Ingress.mkH2c := by
  unfold ingressConn; rw [hasH2Preface_append]; rfl

/-- On a preface-led input the fed bytes are exactly the post-preface bytes. -/
theorem ingressFeed_h2 (bs : Bytes) :
    ingressFeed (h2Preface ++ bs) = bs := by
  unfold ingressFeed; rw [hasH2Preface_append]; exact List.drop_left h2Preface bs

/-! ## (3) The reactor run over the selected connection -/

/-- **The deployed reactor, driven from the protocol-selected connection.** One
recv completion through the PROVEN `Reactor.step` over `deployConfig` — identical
to `Reactor.Deploy.deploySubs` except the initial `Proto.Conn` (and the fed bytes)
are chosen by `ingressConn` / `ingressFeed` rather than hardwired to `mkPlain`. -/
def ingressSubs (input : Bytes) : List RingSubmission :=
  (Reactor.step Reactor.Deploy.deployConfig
      (Proto.State.active (ingressConn input))
      (RingEvent.recvInto 0 (ingressFeed input))).2

/-- On a non-preface input the ingress reactor run is exactly the deployed H1 run
(`deploySubs`) — same config, same `mkPlain` connection, same bytes. -/
theorem ingressSubs_h1 (input : Bytes) (h : hasH2Preface input = false) :
    ingressSubs input = Reactor.Deploy.deploySubs input := by
  unfold ingressSubs
  rw [ingressConn_h1 input h, ingressFeed_h1 input h]
  rfl

/-! ## (4) The guarded serve, over the selected reactor run -/

/-- The deployed response built over an arbitrary submission list and feed bytes:
the real application response (`demoResp`) through the REAL `Header.run` rewrite
(`deployProg` over the proxy/DNS `deployPlan`). On `deploySubs input` / `input`
this is definitionally `Reactor.Deploy.deployResp input`. -/
def ingressResp (subs : List RingSubmission) (feed : Bytes) : Response :=
  Reactor.Lifecycle.rewriteResp
    (Reactor.Deploy.deployProg (Reactor.Deploy.deployPlan subs) feed)
    (demoResp subs)

/-- The REAL Policy/Safety gate on one dispatched request, over the given subs and
feed — the same branch as `Reactor.Deploy.guardOne`, with the response sourced
from `ingressResp` so it composes with the protocol-selected reactor run. -/
def guardOnSubs (subs : List RingSubmission) (feed : Bytes) (req : Proto.Request) : Bytes :=
  match Reactor.Deploy.targetEscapes req with
  | true  => serialize Reactor.Deploy.traversalBlocked404
  | false =>
    match Reactor.Deploy.deployDecisionOf req with
    | none   => serialize Reactor.Deploy.forbidden403
    | some _ => serialize (ingressResp subs feed)

/-- The guarded serve over an arbitrary reactor run: FSM sends forwarded
faithfully; a bare dispatch passes through the REAL gates. Same shape as
`Reactor.Deploy.serveGuarded`, parameterized on the submission list and feed. -/
def serveOverSubs (subs : List RingSubmission) (feed : Bytes) : Bytes :=
  match sendsOf subs with
  | [] =>
    match Reactor.Deploy.dispatchReqOf subs with
    | some req => guardOnSubs subs feed req
    | none     => serialize (ingressResp subs feed)
  | sends => sends.flatten

/-- **The multi-protocol serve.** Select the protocol from the first bytes, run
the reactor from the selected connection, and serve the result through the guarded
pipeline. This is the response function the shipped orb now runs. -/
def serveIngress (input : Bytes) : Bytes :=
  serveOverSubs (ingressSubs input) (ingressFeed input)

/-- Over the deployed H1 run and the whole input, the parameterized guarded serve
is definitionally the deployed `serveGuarded` — `ingressResp (deploySubs input)
input` unfolds to `deployResp input` and `guardOnSubs` to `guardOne`. -/
theorem serveOverSubs_deploySubs (input : Bytes) :
    serveOverSubs (Reactor.Deploy.deploySubs input) input
      = Reactor.Deploy.serveGuarded input := rfl

/-- **`ingress_serves_h1` — the HTTP/1.1 branch is the shipped guarded serve,
byte-for-byte.** On a non-preface input, `serveIngress` equals
`Reactor.Deploy.serveGuarded`, so every guarded seam (403 refuse, 404 traversal,
200 with `x-upstream`/`x-corr`) carries over unchanged. -/
theorem ingress_serves_h1 (input : Bytes) (h : hasH2Preface input = false) :
    serveIngress input = Reactor.Deploy.serveGuarded input := by
  unfold serveIngress
  rw [ingressSubs_h1 input h, ingressFeed_h1 input h]
  exact serveOverSubs_deploySubs input

/-! ## (5) The observed step `main` runs -/

/-- **The guarded, multi-protocol observed step.** `serveIngress` plus the same
REAL observation advance as `Reactor.Deploy.deployStepGuarded` (`Metrics.inc`,
`Tap.step`, the `Trace`-assigned id). This is the function `main` runs. -/
def deployStepIngress (st : Observe.ObsState) (input : Bytes) :
    Bytes × Observe.ObsState :=
  ( serveIngress input
  , { metrics := st.metrics.inc Observe.reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs } )

/-- What `main` writes is definitionally `serveIngress`. -/
theorem deployStepIngress_serves (st : Observe.ObsState) (input : Bytes) :
    (deployStepIngress st input).1 = serveIngress input := rfl

/-- The observed advance is exactly the guarded step's: the REAL `Metrics`
counter moves by one, the REAL `Tap` gate is offered the bytes, and the REAL
`Trace` id is recorded — the multi-protocol step observes identically to the
H1-only guarded step. -/
theorem deployStepIngress_observes (st : Observe.ObsState) (input : Bytes) :
    (deployStepIngress st input).2 = (Reactor.Deploy.deployStepGuarded st input).2 := rfl

/-! ## (6) The seam theorem — the ingress forks on the bytes `main` reads -/

/-- **`ingress_h2_dispatch` — a preface-led input is served by the real H2
engine.** When the post-preface bytes are a well-formed HEADERS frame `bs`
(`H2.decode` completes, HPACK decodes to `d`), the ingress reactor run over
`deployConfig` from the h2c connection emits exactly the dispatch of the
HPACK-decoded request followed by the copy-once recycle — the REAL `h2FeedFn`
executed (via `H2Ingress.h2c_runtime_dispatch`). The `.plainH2` path is entered
and driven, not merely installed. -/
theorem ingress_h2_dispatch (bs payload : Bytes) (sid n : Nat) (es eh : Bool)
    (d : H2.Hpack.Decoded)
    (hframe : H2.decode bs Reactor.H2.h2MaxFrameSize
      = .complete (.headers sid es eh payload) n)
    (hfill : n = bs.length)
    (hhpack : H2.Hpack.decodeHeaderBlock Reactor.H2.h2Huffman Reactor.H2.h2EmptyStore payload
      = .ok d) :
    ingressSubs (h2Preface ++ bs)
      = [ RingSubmission.dispatch (Reactor.H2.requestOfDecoded d)
        , RingSubmission.recycleBuffer 0 ] := by
  unfold ingressSubs
  rw [ingressConn_h2 bs, ingressFeed_h2 bs]
  exact Reactor.H2Ingress.h2c_runtime_dispatch 0 bs payload sid n es eh d hframe hfill hhpack

/-- The H2 serve is driven by that dispatch: `serveIngress` on a preface-led
well-formed HEADERS frame runs the guarded pipeline over the request the real HPACK
decoder produced (`requestOfDecoded d`), so the served bytes answer the H2-decoded
request. -/
theorem ingress_h2_serves (bs payload : Bytes) (sid n : Nat) (es eh : Bool)
    (d : H2.Hpack.Decoded)
    (hframe : H2.decode bs Reactor.H2.h2MaxFrameSize
      = .complete (.headers sid es eh payload) n)
    (hfill : n = bs.length)
    (hhpack : H2.Hpack.decodeHeaderBlock Reactor.H2.h2Huffman Reactor.H2.h2EmptyStore payload
      = .ok d) :
    serveIngress (h2Preface ++ bs)
      = guardOnSubs
          [ RingSubmission.dispatch (Reactor.H2.requestOfDecoded d)
          , RingSubmission.recycleBuffer 0 ]
          bs (Reactor.H2.requestOfDecoded d) := by
  unfold serveIngress
  rw [ingress_h2_dispatch bs payload sid n es eh d hframe hfill hhpack, ingressFeed_h2 bs]
  rfl

/-- **`ingress_selects_protocol` — the shipped exe serves both protocols, chosen
from the first bytes.**

* (H1) A non-preface input is served by the `.plainH1` path: the reactor runs from
  `Proto.Conn.mkPlain`, and `serveIngress` is byte-for-byte the deployed guarded
  serve.
* (H2) A preface-led input whose post-preface bytes are a well-formed HEADERS frame
  is served by the `.plainH2` path: the reactor runs from `H2Ingress.mkH2c` (the
  real `h2Feed` engine) and dispatches the HPACK-decoded request.

The fork is decided by `hasH2Preface` on the very bytes `main` reads, so the one
binary now speaks HTTP/1.1 and h2c prior-knowledge over the same listener. -/
theorem ingress_selects_protocol
    (input : Bytes) (h1 : hasH2Preface input = false)
    (bs payload : Bytes) (sid n : Nat) (es eh : Bool) (d : H2.Hpack.Decoded)
    (hframe : H2.decode bs Reactor.H2.h2MaxFrameSize
      = .complete (.headers sid es eh payload) n)
    (hfill : n = bs.length)
    (hhpack : H2.Hpack.decodeHeaderBlock Reactor.H2.h2Huffman Reactor.H2.h2EmptyStore payload
      = .ok d) :
    (ingressConn input = Proto.Conn.mkPlain
      ∧ serveIngress input = Reactor.Deploy.serveGuarded input)
    ∧ (ingressConn (h2Preface ++ bs) = Reactor.H2Ingress.mkH2c
      ∧ ingressSubs (h2Preface ++ bs)
          = [ RingSubmission.dispatch (Reactor.H2.requestOfDecoded d)
            , RingSubmission.recycleBuffer 0 ]) :=
  ⟨⟨ingressConn_h1 input h1, ingress_serves_h1 input h1⟩,
   ⟨ingressConn_h2 bs, ingress_h2_dispatch bs payload sid n es eh d hframe hfill hhpack⟩⟩

end Ingress
end Reactor
