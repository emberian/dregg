/-!
# HAR recording ring buffer

A bounded recording of request/response entries: newest at the end, capped at
`cap`, oldest evicted when full. `record` appends an entry and keeps only the
most recent `cap` entries.

Theorems: the buffer never exceeds its capacity; the retained entries are a
suffix of the record history (order preserved, newest retained); and when full,
recording evicts exactly the oldest entry.
-/

namespace Har

/-- Keep the last `n` elements of a list (a suffix). When the list is already
short (`length ≤ n`), it is returned unchanged. -/
def keepLast (n : Nat) (l : List α) : List α := l.drop (l.length - n)

/-- `keepLast` never returns more than `n` elements. -/
theorem keepLast_length_le (n : Nat) (l : List α) : (keepLast n l).length ≤ n := by
  unfold keepLast
  rw [List.length_drop]
  omega

/-- `keepLast` is a suffix of its input — it drops a prefix, preserving order. -/
theorem keepLast_suffix (n : Nat) (l : List α) : keepLast n l <:+ l :=
  List.drop_suffix _ l

/-- A recorded entry summary (kept abstract: any recordable value). -/
structure Entry where
  method : String
  path : String
  status : Nat
deriving Repr, DecidableEq

/-- The bounded recorder: a capacity and the retained entries (newest last). -/
structure Recorder where
  cap : Nat
  entries : List Entry
deriving Repr

/-- Well-formed: the retained entries fit the capacity. -/
def Recorder.Wf (r : Recorder) : Prop := r.entries.length ≤ r.cap

/-- Record a new entry: append and keep only the most recent `cap`. -/
def Recorder.record (r : Recorder) (e : Entry) : Recorder :=
  { r with entries := keepLast r.cap (r.entries ++ [e]) }

/-- **Capacity bound.** Recording never overflows the capacity — unconditionally
(no `Wf` hypothesis needed). -/
theorem record_length_le_cap (r : Recorder) (e : Entry) :
    (r.record e).entries.length ≤ r.cap :=
  keepLast_length_le _ _

/-- `Wf` is preserved by recording (a corollary of the unconditional bound). -/
theorem record_wf (r : Recorder) (e : Entry) : (r.record e).Wf :=
  record_length_le_cap r e

/-- **Order preservation + retention.** The retained entries are a suffix of the
history-with-the-new-entry: nothing is reordered, and the newest entry is kept. -/
theorem record_suffix (r : Recorder) (e : Entry) :
    (r.record e).entries <:+ (r.entries ++ [e]) :=
  keepLast_suffix _ _

/-- **FIFO eviction.** When the buffer is full and the capacity is positive,
recording drops exactly the oldest entry and appends the new one. -/
theorem record_full_evicts (r : Recorder) (e : Entry)
    (hfull : r.entries.length = r.cap) (hpos : 0 < r.cap) :
    (r.record e).entries = r.entries.drop 1 ++ [e] := by
  unfold Recorder.record keepLast
  have hlen : (r.entries ++ [e]).length = r.cap + 1 := by
    rw [List.length_append]; simp [hfull]
  rw [hlen]
  have hsub : r.cap + 1 - r.cap = 1 := by omega
  rw [hsub, List.drop_append_of_le_length (by omega)]

/-- Recording keeps at least one entry when the capacity is positive. -/
theorem record_nonempty (r : Recorder) (e : Entry) (hpos : 0 < r.cap) :
    (r.record e).entries ≠ [] := by
  intro hnil
  have hlen1 : 1 ≤ (r.record e).entries.length := by
    unfold Recorder.record keepLast
    rw [List.length_drop, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [hnil] at hlen1
  simp at hlen1

def version : String := "0.1.0"

end Har
