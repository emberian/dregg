import Proto.Basic
import Proto.Step
import Ws.Frame
import Ws.Length
import Ws.Mask
import Ws.Reassembly

/-!
# Reactor.Ws — wiring the real `Ws` library into the FSM WebSocket codec

The audit shape: `Proto.Config.wsFeed`/`wsEncode` are abstract fields, and
`Reactor.Config.demoConfig` stubs them to inert totals (empty decode, empty
encode). Every FSM theorem holds "for all codecs," but nothing proved a *real*
WebSocket frame decoder — unmask + fragmentation reassembly — reaches the
`deliverFrame` outputs the FSM emits. This file closes that gap without touching
`Reactor/Config.lean`: a config transformer `wireWs` overrides exactly the two
WebSocket fields with adapters that drive the real `Ws` library, and a seam
theorem shows a fragmented message delivered across feeds is reassembled by the
real `Ws.Reassembly` engine into the payload the FSM delivers.

## What the real library supplies (and what this adapter builds)

The `Ws` library proves the *pieces*: `Ws.Length.decodeLenField` (the payload
length ladder, canonical + decode-inverts-encode), `Ws.Mask.applyMask` (the
unmask involution), `Ws.Opcode.ofNat` (total opcode classification), and
`Ws.Reassembly.step` (the fragmentation FSM with the in-order-concat theorem
`assemble_join_message`). It does **not** ship a byte-level frame cutter — that
is the adapter's job here, and it is written to call exactly those proven
pieces: `decodeFrame` reads the RFC 6455 §5.2 header, resolves the length with
`decodeLenField`, and unmasks the payload with `applyMask`.

## The reassembly core is the wired field's engine

`feedFrames` folds `Ws.Reassembly.step` over the decoded frames, threading the
reassembly state that lives in `WsCodec.reasm`. `wsFeedFn` — the function
`wireWs` installs — is *defined* as `decodeAll` then `feedFrames`, so the
reassembly the FSM runs is literally the real library's `step` (theorems
`wsFeedFn_frames`/`wsFeedFn_reasm` are `rfl`). Because the state rides in
`WsCodec` and the FSM stores `w.codec` back into `plainWs`/`tlsWs`, a fragment
left mid-assembly persists to the next `bytesReceived` feed — `feedFrames_append`
is the cross-feed lemma.

## Seam theorems

* `feedFrames_fragmented` — the real reassembly concat: an initial data frame,
  a run of continuation frames, and a final `fin` continuation reassemble to the
  in-order concatenation of their payloads (built on `Ws.Reassembly`'s own
  `runAbsorb`/`step_continuation_final`).
* `feedFrames_control_transparent` — a control frame interleaved between
  fragments leaves the reassembly-in-progress state untouched and is delivered
  as-is (control frames interleave transparently, §5.4/§5.5).
* `ws_reassembly_seam` — for a config wired by `wireWs`, `wsFeed` on a byte feed
  whose decode is a fragmented message yields exactly the reassembled payload as
  the single delivered frame, ending idle.
* `wsBytes_seam` — the same, one layer up: the real FSM helper `Proto.wsBytes`
  driven by the wired config emits that reassembled payload as its
  `deliverFrame` output.

Plus a concrete end-to-end `example`: real masked-frame bytes → `wsFeedFn` →
reassembled `"Hi"`, checked by the kernel (`rfl`), so the byte path is grounded,
not just the frame-level algebra.
-/

namespace Reactor
namespace Ws

open Proto (WsCodec WsFrame WsOut Config)
open _root_.Ws (Frame Opcode)
open _root_.Ws.Reassembly (State Partial)

/-! ## Byte-level frame decode — driving the real length ladder and unmask -/

/-- The wire nibble of an opcode (inverse of `Ws.Opcode.ofNat` on the defined
opcodes; `reserved n` carries its raw nibble). Used by the encoder. -/
def opcodeNat : Opcode → Nat
  | .continuation => 0x0
  | .text => 0x1
  | .binary => 0x2
  | .close => 0x8
  | .ping => 0x9
  | .pong => 0xA
  | .reserved n => n

/-- Decode one RFC 6455 §5.2 frame from the head of a byte string: FIN and the
classified opcode from byte 0, the mask bit and 7-bit length from byte 1, the
extended-length rung resolved by the real `Ws.decodeLenField`, and the payload
unmasked by the real `Ws.applyMask` when the mask bit is set. Returns the
decoded `Ws.Frame` and the unconsumed tail, or `none` if the buffer holds no
complete frame yet (a partial header or a short payload). -/
def decodeFrame : List UInt8 → Option (Frame × List UInt8)
  | b0 :: b1 :: rest0 =>
    let n0 := b0.toNat
    let n1 := b1.toNat
    let fin := (n0 &&& 0x80) != 0
    let opcode := Opcode.ofNat (n0 &&& 0x0f)
    let masked := (n1 &&& 0x80) != 0
    let len7 := n1 &&& 0x7f
    let extCount := if len7 = 126 then 2 else if len7 = 127 then 8 else 0
    let ext := rest0.take extCount
    if ext.length < extCount then none
    else
      let rest1 := rest0.drop extCount
      let payloadLen := _root_.Ws.decodeLenField len7 ext
      let keyLen := if masked then 4 else 0
      let key := rest1.take keyLen
      if key.length < keyLen then none
      else
        let rest2 := rest1.drop keyLen
        let raw := rest2.take payloadLen
        if raw.length < payloadLen then none
        else
          let payload := if masked then _root_.Ws.applyMask key raw else raw
          some ({ fin := fin, opcode := opcode, payload := payload }, rest2.drop payloadLen)
  | _ => none

/-- Cut all complete frames from the head of a buffer, returning the decoded
frames and the undecoded leftover (a partial frame the decoder buffers for the
next feed). Fueled by the buffer length — each successful `decodeFrame` consumes
at least the two header bytes, so the fuel never runs out early on a
well-formed stream. -/
def decodeAllAux : Nat → List UInt8 → List Frame × List UInt8
  | 0, bs => ([], bs)
  | fuel + 1, bs =>
    match decodeFrame bs with
    | some (f, rest) =>
      let (fs, leftover) := decodeAllAux fuel rest
      (f :: fs, leftover)
    | none => ([], bs)

/-- Decode every complete frame in a buffer; the second component is the
partial-frame leftover carried to the next feed. -/
def decodeAll (bs : List UInt8) : List Frame × List UInt8 := decodeAllAux bs.length bs

/-! ## The reassembly core — folding the real `Ws.Reassembly.step` -/

/-- One reassembly output rendered as the FSM-facing delivered frames. A
completed message is delivered as a single logical `fin` frame carrying its
concatenated payload; a control frame is delivered as-is; an absorbed fragment
or a protocol error delivers nothing. -/
def deliverOf : _root_.Ws.Reassembly.Output → List WsFrame
  | .message op payload => [⟨{ fin := true, opcode := op, payload := payload }⟩]
  | .control cf => [⟨cf⟩]
  | .absorbed => []
  | .error => []

/-- Fold `Ws.Reassembly.step` over a list of decoded frames, threading the
reassembly state (the state that lives in `WsCodec.reasm`) and collecting the
frames to deliver. This is the real library's fragmentation engine; `wsFeedFn`
runs exactly this over the decoded frames. -/
def feedFrames : State → List Frame → State × List WsFrame
  | st, [] => (st, [])
  | st, f :: fs =>
    let stepped := _root_.Ws.Reassembly.step st f
    let tail := feedFrames stepped.1 fs
    (tail.1, deliverOf stepped.2 ++ tail.2)

/-- A close control frame (drives `WsOut.closeReceived`). -/
def isCloseFrame (f : Frame) : Bool :=
  match f.opcode with
  | .close => true
  | _ => false

/-! ## The wired codec fields -/

/-- `wsFeed`: append the feed to the codec's partial-frame buffer, cut complete
frames with the real decoder, fold them through the real reassembly engine
starting from the codec's carried state, and report the advanced codec (new
leftover + new reassembly state), the delivered frames, and whether a peer Close
was seen. -/
def wsFeedFn (codec : WsCodec) (bytes : List UInt8) : WsOut :=
  let decoded := decodeAll (codec.recvBuf ++ bytes)
  let fed := feedFrames codec.reasm decoded.1
  { codec := { recvBuf := decoded.2, reasm := fed.1 }
    frames := fed.2
    closeReceived := decoded.1.any isCloseFrame }

/-- `wsEncode`: encode a logical frame to the wire (RFC 6455 §5.2). Server-side
frames are never masked, so the mask bit is `0` and no key is emitted; the
payload length uses the real minimal-rung ladder `Ws.encodeLenField`. -/
def wsEncodeFn (wf : WsFrame) : List UInt8 :=
  let f := wf.frame
  let b0 := UInt8.ofNat ((if f.fin then 0x80 else 0) ||| opcodeNat f.opcode)
  let enc := _root_.Ws.encodeLenField f.payload.length
  let b1 := UInt8.ofNat enc.1
  b0 :: b1 :: (enc.2 ++ f.payload)

/-- The config transformer: install the real WebSocket adapters over any base
config, leaving every other field (the HTTP/1, TLS, HTTP/2, SOCKS lanes)
untouched. `Reactor.Config.demoConfig` is not modified; a caller writes
`wireWs demoConfig` to obtain a config whose WebSocket lane is the real engine. -/
def wireWs (cfg : Config) : Config :=
  { cfg with wsFeed := wsFeedFn, wsEncode := wsEncodeFn }

/-- The wiring is real: `wireWs` installs exactly `wsFeedFn`. -/
theorem wireWs_wsFeed (cfg : Config) : (wireWs cfg).wsFeed = wsFeedFn := rfl

/-- The wiring is real: `wireWs` installs exactly `wsEncodeFn`. -/
theorem wireWs_wsEncode (cfg : Config) : (wireWs cfg).wsEncode = wsEncodeFn := rfl

/-- The delivered frames of a wired feed are exactly the real reassembly fold
over the decoded frames — the FSM's WebSocket delivery *is* `Ws.Reassembly`. -/
theorem wsFeedFn_frames (codec : WsCodec) (bytes : List UInt8) :
    (wsFeedFn codec bytes).frames
      = (feedFrames codec.reasm (decodeAll (codec.recvBuf ++ bytes)).1).2 := rfl

/-- The reassembly state the codec carries forward is exactly the real
reassembly fold's resulting state (persisted across feeds). -/
theorem wsFeedFn_reasm (codec : WsCodec) (bytes : List UInt8) :
    (wsFeedFn codec bytes).codec.reasm
      = (feedFrames codec.reasm (decodeAll (codec.recvBuf ++ bytes)).1).1 := rfl

/-! ## Cross-feed persistence -/

/-- Feeding two batches of frames (as two `wsFeed` calls do, with the reassembly
state persisted in `WsCodec.reasm` between them) equals feeding their
concatenation: the reassembly engine is state-threaded, not reset per feed. -/
theorem feedFrames_append (a : List Frame) : ∀ (st : State) (b : List Frame),
    feedFrames st (a ++ b)
      = ((feedFrames (feedFrames st a).1 b).1,
         (feedFrames st a).2 ++ (feedFrames (feedFrames st a).1 b).2) := by
  induction a with
  | nil => intro st b; simp [feedFrames]
  | cons f a ih =>
    intro st b
    simp only [List.cons_append, feedFrames]
    rw [ih]
    simp [List.append_assoc]

/-! ## Control-frame transparency -/

/-- A single control frame is absorbed by neither reassembly slot: the state is
unchanged and the frame is delivered as-is (via `Ws.Reassembly.step_control_*`). -/
theorem feedFrames_control (st : State) (cf : Frame)
    (h : cf.opcode.isControl = true) : feedFrames st [cf] = (st, [⟨cf⟩]) := by
  have h1 := _root_.Ws.Reassembly.step_control_state st cf h
  have h2 := _root_.Ws.Reassembly.step_control_output st cf h
  simp only [feedFrames]
  rw [h1]
  simp [deliverOf, h2]

/-- **Control frames interleave transparently.** A control frame appended after
any run of frames leaves the reassembly-in-progress state exactly where the run
left it, and appends its own delivery — it cannot disturb a fragment under
construction (RFC 6455 §5.4/§5.5). -/
theorem feedFrames_control_transparent (st : State) (a : List Frame) (cf : Frame)
    (h : cf.opcode.isControl = true) :
    (feedFrames st (a ++ [cf])).1 = (feedFrames st a).1
    ∧ (feedFrames st (a ++ [cf])).2 = (feedFrames st a).2 ++ [⟨cf⟩] := by
  rw [feedFrames_append, feedFrames_control _ cf h]
  exact ⟨rfl, rfl⟩

/-! ## The fragmentation seam -/

/-- Feeding a run of non-final continuation frames from an assembling state
accumulates their payloads in order (all absorbed, nothing delivered) — the
frame-driven companion of `Ws.Reassembly.runAbsorb`. -/
theorem feedFrames_conts (payloads : List (List UInt8)) : ∀ (p : Partial),
    feedFrames (.assembling p)
        (payloads.map (fun m => ({ fin := false, opcode := .continuation, payload := m } : Frame)))
      = (.assembling (_root_.Ws.Reassembly.runAbsorb p payloads), []) := by
  induction payloads with
  | nil => intro p; simp [feedFrames, _root_.Ws.Reassembly.runAbsorb]
  | cons m ms ih =>
    intro p
    simp only [List.map_cons, feedFrames]
    rw [_root_.Ws.Reassembly.step_continuation_absorb]
    simp only [deliverOf, List.nil_append]
    rw [ih]
    simp [_root_.Ws.Reassembly.runAbsorb]

/-- **The reassembly seam (frame level).** A fragmented message — an initial
`text`/`binary` frame with `fin = false`, a run of non-final continuation
frames, and a final `fin` continuation — reassembles, through the real
`Ws.Reassembly` engine, to a single delivered frame whose payload is the
in-order concatenation of every fragment, returning the engine to `idle`. -/
theorem feedFrames_fragmented (op : Opcode) (hop : op = .text ∨ op = .binary)
    (initial : List UInt8) (mids : List (List UInt8)) (final : List UInt8) :
    feedFrames .idle
        (({ fin := false, opcode := op, payload := initial } : Frame)
          :: mids.map (fun m => ({ fin := false, opcode := .continuation, payload := m } : Frame))
          ++ [{ fin := true, opcode := .continuation, payload := final }])
      = (.idle, [⟨{ fin := true, opcode := op,
                    payload := initial ++ mids.flatten ++ final }⟩]) := by
  have hinit : _root_.Ws.Reassembly.step .idle
      ({ fin := false, opcode := op, payload := initial } : Frame)
      = (.assembling { opcode := op, acc := initial }, .absorbed) := by
    rcases hop with h | h <;> subst h <;> rfl
  simp only [List.cons_append, feedFrames]
  rw [hinit]
  simp only [deliverOf, List.nil_append]
  rw [feedFrames_append, feedFrames_conts]
  simp only [feedFrames]
  rw [_root_.Ws.Reassembly.step_continuation_final,
      _root_.Ws.Reassembly.runAbsorb_acc, _root_.Ws.Reassembly.runAbsorb_opcode]
  simp [deliverOf, List.append_assoc]

/-! ## The wired-config seam -/

/-- **`ws_reassembly_seam`.** For a config wired by `wireWs`, feed a byte stream
whose decode is a fragmented WebSocket message (initial data frame, continuation
run, final `fin` continuation) into `wsFeed` on an idle codec. The wired field
delivers exactly one frame — the reassembled message, its payload the in-order
concatenation of every fragment — and carries the reassembly state back to
`idle`. The reassembly is performed by the real `Ws.Reassembly` engine
(`wsFeedFn_frames`/`wsFeedFn_reasm` tie the field to `feedFrames`). -/
theorem ws_reassembly_seam (cfg : Config) (codec : WsCodec) (bytes : List UInt8)
    (op : Opcode) (hop : op = .text ∨ op = .binary)
    (initial : List UInt8) (mids : List (List UInt8)) (final : List UInt8)
    (hidle : codec.reasm = .idle)
    (hdec : (decodeAll (codec.recvBuf ++ bytes)).1
      = ({ fin := false, opcode := op, payload := initial } : Frame)
          :: mids.map (fun m => ({ fin := false, opcode := .continuation, payload := m } : Frame))
          ++ [{ fin := true, opcode := .continuation, payload := final }]) :
    ((wireWs cfg).wsFeed codec bytes).frames
        = [⟨{ fin := true, opcode := op,
              payload := initial ++ mids.flatten ++ final }⟩]
      ∧ ((wireWs cfg).wsFeed codec bytes).codec.reasm = .idle := by
  rw [wireWs_wsFeed]
  refine ⟨?_, ?_⟩
  · rw [wsFeedFn_frames, hidle, hdec, feedFrames_fragmented op hop]
  · rw [wsFeedFn_reasm, hidle, hdec, feedFrames_fragmented op hop]

/-! ## The FSM-level seam -/

/-- A fragmented data message carries no close frame, so `closeReceived` is
`false` and the FSM stays on the WebSocket path (rather than draining). -/
theorem fragmented_no_close (op : Opcode) (hop : op = .text ∨ op = .binary)
    (initial : List UInt8) (mids : List (List UInt8)) (final : List UInt8) :
    (({ fin := false, opcode := op, payload := initial } : Frame)
        :: mids.map (fun m => ({ fin := false, opcode := .continuation, payload := m } : Frame))
        ++ [({ fin := true, opcode := .continuation, payload := final } : Frame)]).any isCloseFrame
      = false := by
  have hop' : isCloseFrame ({ fin := false, opcode := op, payload := initial } : Frame) = false := by
    rcases hop with h | h <;> subst h <;> rfl
  have hfin : isCloseFrame ({ fin := true, opcode := .continuation, payload := final } : Frame) = false :=
    rfl
  have hmids : ∀ (l : List (List UInt8)),
      (l.map (fun m => ({ fin := false, opcode := .continuation, payload := m } : Frame))).any isCloseFrame
        = false := by
    intro l
    induction l with
    | nil => rfl
    | cons m ms ih => simp only [List.map_cons, List.any_cons, ih, Bool.or_false]; rfl
  simp only [List.any_cons, List.any_append, List.any_nil, hop', hfin, hmids,
    Bool.or_false, Bool.false_or, Bool.or_self]

/-- **`wsBytes_seam`.** One layer up from the field: the real FSM WebSocket
helper `Proto.wsBytes`, driven by the `wireWs`-wired config over a byte feed that
decodes to a fragmented message, emits exactly one output — a `deliverFrame`
carrying the reassembled payload — and lands on the `plainWs` successor with the
codec's reassembly state back to `idle`. This is the anti-island composition:
real config field → real FSM helper → the payload the machine delivers. -/
theorem wsBytes_seam (cfg : Config) (codec : WsCodec) (bytes : List UInt8)
    (op : Opcode) (hop : op = .text ∨ op = .binary)
    (initial : List UInt8) (mids : List (List UInt8)) (final : List UInt8)
    (hidle : codec.reasm = .idle)
    (hdec : (decodeAll (codec.recvBuf ++ bytes)).1
      = ({ fin := false, opcode := op, payload := initial } : Frame)
          :: mids.map (fun m => ({ fin := false, opcode := .continuation, payload := m } : Frame))
          ++ [{ fin := true, opcode := .continuation, payload := final }]) :
    (Proto.wsBytes (wireWs cfg) Proto.ProtoState.plainWs codec bytes).outs
      = [Proto.Output.deliverFrame
          (⟨{ fin := true, opcode := op,
              payload := initial ++ mids.flatten ++ final }⟩ : WsFrame)] := by
  have hframes : ((wireWs cfg).wsFeed codec bytes).frames
      = [⟨{ fin := true, opcode := op, payload := initial ++ mids.flatten ++ final }⟩] :=
    (ws_reassembly_seam cfg codec bytes op hop initial mids final hidle hdec).1
  have hclose : ((wireWs cfg).wsFeed codec bytes).closeReceived = false := by
    rw [wireWs_wsFeed]
    show (decodeAll (codec.recvBuf ++ bytes)).1.any isCloseFrame = false
    rw [hdec]
    exact fragmented_no_close op hop initial mids final
  simp only [Proto.wsBytes, hclose, hframes]
  rw [if_neg (by decide : ¬ (false = true))]
  rfl

/-! ## Concrete end-to-end byte grounding

A real two-frame fragmented text message `"Hi"` on the wire (unmasked, minimal
lengths): frame 1 `[0x01,0x01,0x48]` (`fin=0`, opcode `text`, payload `"H"`),
frame 2 `[0x80,0x01,0x69]` (`fin=1`, opcode `continuation`, payload `"i"`). Fed
to `wsFeedFn` on a fresh codec, the kernel reduces the whole path — decode,
unmask (trivial here), length ladder, reassembly — to the delivered message
`"Hi"`, with the codec back to idle and no leftover. This grounds the byte path
concretely, not just the frame-level algebra. -/
example :
    wsFeedFn { recvBuf := [], reasm := .idle } [0x01, 0x01, 0x48, 0x80, 0x01, 0x69]
      = { codec := { recvBuf := [], reasm := .idle }
          frames := [⟨{ fin := true, opcode := .text, payload := [0x48, 0x69] }⟩]
          closeReceived := false } := rfl

/-- A masked client→server single frame decodes to its unmasked payload through
the real `Ws.applyMask`: key `[0x01,0x02,0x03,0x04]` over masked bytes recovers
`[0x48,0x49]` (`"HI"`). `fin=1`, opcode `text`, mask bit set, len 2. -/
example :
    decodeFrame [0x81, 0x82, 0x01, 0x02, 0x03, 0x04, 0x49, 0x4B]
      = some ({ fin := true, opcode := .text, payload := [0x48, 0x49] }, []) := rfl

end Ws
end Reactor
