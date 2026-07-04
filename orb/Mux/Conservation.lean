import Mux.Priority

/-!
# Mux.Conservation — multiplexing conserves bytes

Multiplexing many streams onto one connection emits a single tagged wire: a
sequence of `(StreamId × UInt8)` — each byte carries the id of the stream that
produced it. A `sends` schedule is the actual serve order the scheduler chose:
a list of `(StreamId, chunk)` where each chunk is the bytes served from that
stream on its turn. Chunks from a stream may be split apart and interleaved
with any others.

* `wireOf` lays every scheduled chunk onto the wire, byte-by-byte, tagged.
* `demux` de-interleaves the wire by stream id.
* `payloadOf` is a stream's in-order payload: its chunks (in serve order)
  concatenated.

The conservation theorem `demux_wireOf` states that **de-interleaving recovers
each stream's payload exactly**, for *any* interleaving `sends`:

```
demux (wireOf sends) k = payloadOf sends k
```

Because `payloadOf … k` reads only the `k`-tagged sends, this is also
no-cross-stream-corruption: bytes of one stream never leak into another's
reconstruction. `wireOf_length` is the byte-count form: the wire is exactly as
long as the sum of the payloads (nothing added, nothing dropped).
-/

namespace Mux
namespace Conservation

/-- The multiplexed wire: every scheduled chunk laid down byte-by-byte, each
byte tagged with its stream id, in serve order. -/
def wireOf : List (StreamId × List UInt8) → List (StreamId × UInt8)
  | [] => []
  | (sid, bs) :: rest => bs.map (fun b => (sid, b)) ++ wireOf rest

/-- De-interleave the wire by stream id: keep this stream's bytes, in order. -/
def demux : List (StreamId × UInt8) → StreamId → List UInt8
  | [], _ => []
  | (sid, byte) :: rest, k =>
    if sid == k then byte :: demux rest k else demux rest k

/-- A stream's in-order payload: its scheduled chunks concatenated. -/
def payloadOf : List (StreamId × List UInt8) → StreamId → List UInt8
  | [], _ => []
  | (sid, bs) :: rest, k =>
    if sid == k then bs ++ payloadOf rest k else payloadOf rest k

/-- The total scheduled byte count. -/
def totalBytes : List (StreamId × List UInt8) → Nat
  | [] => 0
  | (_, bs) :: rest => bs.length + totalBytes rest

/-! ## Structural lemmas -/

/-- De-interleaving distributes over wire concatenation. -/
theorem demux_append (w1 w2 : List (StreamId × UInt8)) (k : StreamId) :
    demux (w1 ++ w2) k = demux w1 k ++ demux w2 k := by
  induction w1 with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨sid, byte⟩ := hd
    cases hkv : (sid == k) with
    | true => simp [demux, hkv, ih]
    | false => simp [demux, hkv, ih]

/-- De-interleaving a single tagged chunk: all `sid`, so it survives iff
`sid == k`. -/
theorem demux_tag (sid : StreamId) (bs : List UInt8) (k : StreamId) :
    demux (bs.map (fun b => (sid, b))) k = if sid == k then bs else [] := by
  induction bs with
  | nil => cases hkv : (sid == k) <;> simp [demux, hkv]
  | cons b bs ih =>
    simp only [List.map_cons]
    cases hkv : (sid == k) with
    | true => simp [demux, hkv, ih]
    | false => simp [demux, hkv, ih]

/-! ## Byte conservation -/

/-- **Conservation of bytes (content).** For any interleaving `sends`, the wire
de-interleaved by stream id equals that stream's in-order payload. No bytes are
lost, duplicated, reordered, or cross-contaminated between streams. -/
theorem demux_wireOf (sends : List (StreamId × List UInt8)) (k : StreamId) :
    demux (wireOf sends) k = payloadOf sends k := by
  induction sends with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨sid, bs⟩ := hd
    simp only [wireOf, payloadOf]
    rw [demux_append, demux_tag, ih]
    cases hkv : (sid == k) <;> simp [hkv]

/-- **Conservation of bytes (count).** The wire length equals the sum of the
scheduled chunk lengths. -/
theorem wireOf_length (sends : List (StreamId × List UInt8)) :
    (wireOf sends).length = totalBytes sends := by
  induction sends with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨sid, bs⟩ := hd
    simp [wireOf, totalBytes, List.length_append, List.length_map, ih]

/-- **No cross-stream corruption, explicitly.** A stream `k`'s reconstruction is
unaffected by chunks tagged with any other id `j ≠ k`: prepending a `j`-chunk to
the schedule leaves `demux … k` unchanged. -/
theorem demux_other_noop (sid : StreamId) (bs : List UInt8)
    (rest : List (StreamId × List UInt8)) (k : StreamId) (h : sid ≠ k) :
    demux (wireOf ((sid, bs) :: rest)) k = demux (wireOf rest) k := by
  simp only [wireOf]
  rw [demux_append, demux_tag]
  have : (sid == k) = false := by
    cases hkv : (sid == k) with
    | true => exact absurd (beq_iff_eq.mp hkv) h
    | false => rfl
  simp [this]

/-! ## Checker-verified vectors -/

/-- Two streams interleaved byte-wise still de-interleave cleanly. -/
example :
    demux (wireOf [(1, [10, 11]), (2, [20]), (1, [12])]) 1 = [10, 11, 12] := rfl
example :
    demux (wireOf [(1, [10, 11]), (2, [20]), (1, [12])]) 2 = [20] := rfl
/-- A silent stream de-interleaves to nothing. -/
example : demux (wireOf [(1, [10, 11]), (2, [20])]) 3 = [] := rfl

end Conservation
end Mux
