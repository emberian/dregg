import Proto.Step
import H2.Frame
import H2.Hpack
import H2.Stream

/-!
# Reactor.H2 — wiring the real HTTP/2 engine into the connection FSM

The H2 lane's `Config` fields (`h2Init`/`h2Feed`/`h2Send`) were inert stubs:
`h2Init := ⟨0⟩`, `h2Feed := fun h2c _ => (h2c, [])`. Every FSM theorem held
"for all codecs," but the real H2 library (`H2/Frame.lean` frame decoder,
`H2/Hpack.lean` HPACK-into-arena decode, `H2/Stream.lean` per-stream FSM) was
never invoked on the reactor path. This file closes that gap.

`Proto.H2Conn` now carries a real framing-engine state — the undecoded
partial-frame buffer plus the per-stream `H2.Stream.StreamState` table. This
file supplies the concrete engine functions that drive that state:

* `framePump` — decode as many whole frames as the buffer holds (real
  `H2.Frame.decode`), advancing the per-stream FSM and emitting `Proto.H2Event`s.
* `h2FeedFn` — the `Config.h2Feed` realization: append plaintext, pump frames.
  On a HEADERS frame it runs the **real HPACK decode into a fresh arena**
  (`H2.Hpack.decodeHeaderBlock`) and resolves the decoded head — the pseudo
  `:method`/`:path` and the regular fields — back to bytes into a
  `Proto.Request`.
* `h2SendFn` — the `Config.h2Send` realization: encode a real DATA frame.

`Reactor.Config.demoConfig` wires `h2Feed := h2FeedFn` (checkable by `rfl`), so
the running reactor's `Proto.onBytes … (.plainH2 …)` / `… (.tlsH2 …)` path now
invokes this engine.

## The seam theorem — `h2_frame_seam`

A well-formed H2 HEADERS frame decoded by the real H2 lib, fed through any
config whose `h2Feed` is `h2FeedFn`, yields an FSM `H2Event.headers` whose
`Request` carries the HPACK-decoded head, and the decode preserves store
well-formedness (`d.store.Wf`). Composed with the FSM's `plainH2` handling this
becomes a `Output.dispatch` of that request; `h2_seam_reactor` carries it all
the way to `Proto.step` on a `bytesReceived` input — the actual running-reactor
transition.
-/

namespace Reactor
namespace H2

open Proto (H2Conn H2Event Request Bytes Output)

/-- The peer's advertised `SETTINGS_MAX_FRAME_SIZE` (RFC 9113 §4.2 default). -/
def h2MaxFrameSize : Nat := 16384

/-- The Huffman decoder plugged into the HPACK decode. Reject-all: the theorems
hold for *every* decoder behavior (`H2.Hpack` axiomatizes the interface), and
the seam vectors avoid the Huffman bit. -/
def h2Huffman : H2.Hpack.HuffmanDecoder := ⟨fun _ => none⟩

/-- A fresh empty arena the HPACK decode of one header block writes into. -/
def h2EmptyStore : Arena.Store := { main := #[], sidecar := #[], entries := [] }

/-- The empty store is well-formed (no entries to be out of bounds). -/
theorem h2EmptyStore_wf : h2EmptyStore.Wf := by
  intro e he; nomatch he

/-- The HTTP/2 pseudo-version string carried in the resolved request. -/
def h2Version : Bytes := (String.toUTF8 "HTTP/2").toList

/-! ## Resolving the HPACK-decoded head into a `Proto.Request` -/

/-- Resolve one arena view entry to its bytes through the proven-total
`Store.resolve`. Under `Wf` (which `decodeHeaderBlock_wf` gives) the `none`
arm is dead for the emitted entries. -/
def resolveBytes (s : Arena.Store) (e : Arena.Entry) : Bytes :=
  match s.resolve e with
  | some b => b.toList
  | none => []

/-- Build the `Proto.Request` denoted by an HPACK-decoded header block: the
`:method` and `:path` pseudo-headers fill `method`/`target`, the regular fields
fill `headers` (each resolved back to bytes), and `version` is the fixed HTTP/2
marker. This is the single point that fills the request head; the seam theorem
and the engine both reference it, so they cannot drift. -/
def requestOfDecoded (d : H2.Hpack.Decoded) : Request :=
  { method  := (d.pseudo.method.map (resolveBytes d.store)).getD []
    target  := (d.pseudo.path.map (resolveBytes d.store)).getD []
    version := h2Version
    headers := d.fields.map fun fl =>
      (resolveBytes d.store fl.name, resolveBytes d.store fl.value) }

/-! ## The per-stream FSM table -/

/-- The current FSM state of stream `sid` (unseen streams are `idle`). -/
def streamState (streams : List (Nat × H2.Stream.StreamState)) (sid : Nat) :
    H2.Stream.StreamState :=
  match streams.find? (fun q => q.1 == sid) with
  | some (_, s) => s
  | none => .idle

/-- Install `s` as the FSM state of stream `sid`. -/
def setStream (streams : List (Nat × H2.Stream.StreamState)) (sid : Nat)
    (s : H2.Stream.StreamState) : List (Nat × H2.Stream.StreamState) :=
  (sid, s) :: streams.filter (fun q => q.1 != sid)

/-- Advance stream `sid` by one FSM event (real `H2.Stream.stepState`). -/
def driveStream (streams : List (Nat × H2.Stream.StreamState)) (sid : Nat)
    (ev : H2.Stream.Event) : List (Nat × H2.Stream.StreamState) :=
  setStream streams sid (H2.Stream.stepState (streamState streams sid) ev)

/-! ## From a decoded frame to stream-table update + FSM events -/

/-- Interpret one decoded `H2.Frame` against the per-stream FSM table: HEADERS
runs the real HPACK decode and drives `recvHeaders`; DATA drives `recvData`;
RST_STREAM drives `recvRstStream`; WINDOW_UPDATE and GOAWAY surface control
events. Frame types the FSM `H2Event` vocabulary does not model produce no
event. A HPACK error becomes a connection-level `protoError`. -/
def stepFrame (streams : List (Nat × H2.Stream.StreamState)) :
    H2.Frame → List (Nat × H2.Stream.StreamState) × List H2Event
  | .headers sid es _eh payload =>
    match H2.Hpack.decodeHeaderBlock h2Huffman h2EmptyStore payload with
    | .ok d =>
      (driveStream streams sid (.recvHeaders es),
        [H2Event.headers sid (requestOfDecoded d) es])
    | .error _ => (streams, [H2Event.protoError])
  | .data sid es payload =>
    (driveStream streams sid (.recvData es), [H2Event.data sid payload es])
  | .rstStream sid _ => (driveStream streams sid .recvRstStream, [])
  | .windowUpdate _ _ => (streams, [H2Event.windowUpdate])
  | .goaway _ _ => (streams, [H2Event.goaway])
  | .priority _ _ => (streams, [])
  | .settings _ _ _ => (streams, [])
  | .pushPromise _ _ => (streams, [])
  | .ping _ _ _ => (streams, [])
  | .continuation _ _ _ => (streams, [])
  | .unknown _ _ _ => (streams, [])

/-! ## The frame pump -/

/-- Decode as many whole frames as `buf` holds, driving the FSM and collecting
events in wire order; returns the undecoded remainder (a partial frame kept for
the next feed), the advanced stream table, and the events. Fuel is
`buf.length + 1` at the call sites — more than the number of frames, since each
completed frame consumes at least the 9-octet header. -/
def framePump : Nat → List (Nat × H2.Stream.StreamState) → Bytes →
    Bytes × List (Nat × H2.Stream.StreamState) × List H2Event
  | 0, streams, buf => (buf, streams, [])
  | fuel + 1, streams, buf =>
    match H2.decode buf h2MaxFrameSize with
    | .complete f n =>
      let (streams', evs) := stepFrame streams f
      let (buf', streams'', evs') := framePump fuel streams' (buf.drop n)
      (buf', streams'', evs ++ evs')
    | .incomplete => (buf, streams, [])
    | .tooLarge _ => (buf, streams, [H2Event.protoError])
    | .error => (buf, streams, [H2Event.protoError])

/-- On an empty buffer the pump halts with no events (the decoder reports
`incomplete` on fewer than 9 octets). -/
theorem framePump_nil (fuel : Nat) (streams : List (Nat × H2.Stream.StreamState)) :
    framePump fuel streams [] = ([], streams, []) := by
  cases fuel <;> rfl

/-- One-step unfolding of the pump on a completed frame decode. -/
theorem framePump_complete (fuel : Nat)
    (streams : List (Nat × H2.Stream.StreamState)) (buf : Bytes)
    (f : H2.Frame) (n : Nat)
    (h : H2.decode buf h2MaxFrameSize = .complete f n) :
    framePump (fuel + 1) streams buf
      = (let (streams', evs) := stepFrame streams f
         let (buf', streams'', evs') := framePump fuel streams' (buf.drop n)
         (buf', streams'', evs ++ evs')) := by
  simp only [framePump, h]

/-! ## The `Config.h2Feed` / `Config.h2Send` realizations -/

/-- `Config.h2Feed`: accumulate plaintext into the framing buffer, then pump. -/
def h2FeedFn (h2c : H2Conn) (plain : Bytes) : H2Conn × List H2Event :=
  let buf := h2c.recvBuf ++ plain
  let r := framePump (buf.length + 1) h2c.streams buf
  ({ recvBuf := r.1, streams := r.2.1 }, r.2.2)

/-- The fresh engine for a newly negotiated HTTP/2 connection. -/
def h2InitVal : H2Conn := {}

/-! ### DATA-frame encode for the send path -/

/-- Big-endian 24-bit length field. -/
def u24 (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- Big-endian 31-bit stream-id word (reserved high bit clear). -/
def u31 (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 16777216 % 128), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- Encode one DATA frame (END_STREAM set): the 9-octet header then the
payload (RFC 9113 §6.1). -/
def encodeDataFrame (sid : Nat) (payload : Bytes) : Bytes :=
  u24 payload.length ++ [0x00, 0x01] ++ u31 sid ++ payload

/-- `Config.h2Send`: frame the response bytes as a DATA frame and advance the
stream FSM by `sendData`. Payloads within one frame; the window is assumed open
(no flow-block remainder) at this rung — the flow-control model lives in
`H2/FlowControl.lean`. -/
def h2SendFn (h2c : H2Conn) (sid : Nat) (payload : Bytes) :
    H2Conn × Bytes × Option Bytes :=
  ({ h2c with streams := driveStream h2c.streams sid (.sendData true) },
    encodeDataFrame sid payload, none)

/-! ## The seam -/

/-- **Engine-level seam**: a HEADERS frame that fills `bs`, whose HPACK payload
decodes to `d`, is turned by the real engine into exactly one FSM event — the
`H2Event.headers` carrying the HPACK-decoded request. -/
theorem h2FeedFn_singleHeaders
    (bs payload : Bytes) (sid n : Nat) (es eh : Bool) (d : H2.Hpack.Decoded)
    (hframe : H2.decode bs h2MaxFrameSize = .complete (.headers sid es eh payload) n)
    (hfill : n = bs.length)
    (hhpack : H2.Hpack.decodeHeaderBlock h2Huffman h2EmptyStore payload = .ok d) :
    h2FeedFn h2InitVal bs
      = ({ recvBuf := [], streams := driveStream [] sid (.recvHeaders es) },
         [H2Event.headers sid (requestOfDecoded d) es]) := by
  subst n
  have hbuf : h2FeedFn h2InitVal bs
      = ({ recvBuf := (framePump (bs.length + 1) [] bs).1,
           streams := (framePump (bs.length + 1) [] bs).2.1 },
         (framePump (bs.length + 1) [] bs).2.2) := rfl
  rw [hbuf, framePump_complete bs.length [] bs _ _ hframe]
  simp only [stepFrame, hhpack, List.drop_length, framePump_nil, List.append_nil]

/-- **Composition seam** (`plainH2` path of the running FSM): fed through any
config whose `h2Feed` is `h2FeedFn`, a single well-formed HEADERS frame makes
`Proto.onBytes` dispatch the HPACK-decoded request, without closing — and the
HPACK decode preserved store well-formedness. -/
theorem h2_frame_seam {cfg : Proto.Config} (hcfg : cfg.h2Feed = h2FeedFn)
    (bs payload : Bytes) (sid n : Nat) (es eh : Bool) (d : H2.Hpack.Decoded)
    (hframe : H2.decode bs h2MaxFrameSize = .complete (.headers sid es eh payload) n)
    (hfill : n = bs.length)
    (hhpack : H2.Hpack.decodeHeaderBlock h2Huffman h2EmptyStore payload = .ok d) :
    (Proto.onBytes cfg (.plainH2 h2InitVal []) bs).outs
        = [Output.dispatch (requestOfDecoded d)]
      ∧ (Proto.onBytes cfg (.plainH2 h2InitVal []) bs).closeNow = false
      ∧ d.store.Wf := by
  have hfeed : cfg.h2Feed h2InitVal bs = (h2FeedFn h2InitVal bs) := by rw [hcfg]
  have hpair := h2FeedFn_singleHeaders bs payload sid n es eh d hframe hfill hhpack
  refine ⟨?_, ?_, ?_⟩
  · show (Proto.runH2 cfg .plainH2 h2InitVal [] bs []).outs = _
    unfold Proto.runH2
    rw [hfeed, hpair]
    simp only [Proto.h2Apply, List.nil_append]
  · show (Proto.runH2 cfg .plainH2 h2InitVal [] bs []).closeNow = _
    unfold Proto.runH2
    rw [hfeed, hpair]
    simp only [Proto.h2Apply]
  · exact H2.Hpack.decodeHeaderBlock_wf h2Huffman h2EmptyStore payload d h2EmptyStore_wf hhpack

/-- **Running-reactor seam**: the full `Proto.step` on a `bytesReceived` input,
from a connection parked in `plainH2` with the fresh engine and an unblocked
send path, emits exactly the dispatch of the HPACK-decoded request — the real
H2 frame decode + HPACK arena decode wired into the actual transition
function. -/
theorem h2_seam_reactor {cfg : Proto.Config} (hcfg : cfg.h2Feed = h2FeedFn)
    (bs payload : Bytes) (sid n : Nat) (es eh : Bool) (d : H2.Hpack.Decoded)
    (c : Proto.Conn)
    (hframe : H2.decode bs h2MaxFrameSize = .complete (.headers sid es eh payload) n)
    (hfill : n = bs.length)
    (hhpack : H2.Hpack.decodeHeaderBlock h2Huffman h2EmptyStore payload = .ok d)
    (hproto : c.proto = .plainH2 h2InitVal []) (hblk : c.sendBlocked = false) :
    (Proto.step cfg (.active c) (.bytesReceived bs)).2
      = [Output.dispatch (requestOfDecoded d)] := by
  obtain ⟨houts, hclose, _⟩ := h2_frame_seam hcfg bs payload sid n es eh d hframe hfill hhpack
  show (Proto.finish c (Proto.onBytes cfg c.proto bs)).2 = _
  rw [hproto]
  unfold Proto.finish Proto.gate
  rw [hblk, houts, hclose]
  simp only [Bool.false_eq_true, if_false, List.filter_cons]

end H2
end Reactor
