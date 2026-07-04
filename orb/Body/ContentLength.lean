import Body.Basic

/-!
# Content-Length body framing (RFC 7230 §3.3.2)

A `Content-Length` body has a known total `N`: the reader must deliver exactly
the length-`N` prefix of the input stream, in order, and stop — any bytes past
`N` belong to the next message (a pipelined request), not this body.

The reader is a streaming FSM. Its state is `(total, delivered)`, with the
awaited count `remaining = total - delivered.length` derived and the terminal
`complete` state reached when `delivered.length = total`. `feed` folds one input
segment into the state, appending at most `remaining` bytes so the delivered
prefix never overshoots.

Theorems:

* `feed_wf` — the invariant `delivered.length ≤ total` is preserved: the reader
  never delivers more than `Content-Length` bytes.
* `feed_delivered` — one `feed` extends the delivered prefix in order: after
  feeding, `delivered = (old delivered ++ segment).take total`.
* `runFeed_delivered` — folding a stream of segments delivers exactly the
  length-`total` prefix of their concatenation: `delivered = flatten.take total`.
* `complete_delivers_prefix` — **bytes conserved (theorem 1)**: once the input
  carries at least `total` bytes, the reader is `complete`, has delivered
  exactly `total` bytes, and those bytes are precisely `input.take total`; the
  untouched tail `input.drop total` reassembles the input
  (`delivered ++ tail = input`) and never leaks into the body.
* `incomplete_not_complete` — **theorem 4**: a stream shorter than `total`
  leaves the reader in a non-terminal (`complete = false`) state.
-/

namespace Body
namespace ContentLength

/-- Streaming reader state: the fixed `Content-Length` total and the body bytes
delivered so far. -/
structure Reader where
  total : Nat
  delivered : Bytes
deriving Repr, DecidableEq

/-- The initial reader for a `Content-Length` of `n`: nothing delivered yet. -/
def Reader.init (n : Nat) : Reader := { total := n, delivered := [] }

/-- Bytes still awaited before the body is complete. -/
def Reader.remaining (r : Reader) : Nat := r.total - r.delivered.length

/-- Terminal state: exactly `total` bytes have been delivered. -/
def Reader.complete (r : Reader) : Bool := decide (r.delivered.length = r.total)

/-- Feed one input segment. At most `remaining` bytes are appended to the
delivered prefix, so the reader never overshoots `total`; the tail of `seg` past
`remaining` is leftover for the next message and is not part of this body. -/
def Reader.feed (r : Reader) (seg : Bytes) : Reader :=
  { r with delivered := r.delivered ++ seg.take r.remaining }

/-- The reader well-formedness invariant: never more delivered than the total. -/
def Reader.Wf (r : Reader) : Prop := r.delivered.length ≤ r.total

/-- The initial reader is well-formed. -/
theorem init_wf (n : Nat) : (Reader.init n).Wf := by
  simp [Reader.init, Reader.Wf]

/-- `feed` preserves the invariant: the delivered length never exceeds `total`. -/
theorem feed_wf (r : Reader) (seg : Bytes) (h : r.Wf) : (r.feed seg).Wf := by
  have hle : (seg.take r.remaining).length ≤ r.remaining := by
    rw [List.length_take]; exact Nat.min_le_left _ _
  simp only [Reader.Wf, Reader.feed, Reader.remaining, List.length_append] at *
  omega

/-- One `feed` extends the delivered prefix in order: the new delivered bytes are
exactly the length-`total` prefix of the old delivered bytes followed by the
segment. Nothing is reordered; delivery is front-to-back. -/
theorem feed_delivered (r : Reader) (seg : Bytes) (h : r.Wf) :
    (r.feed seg).delivered = (r.delivered ++ seg).take r.total := by
  simp only [Reader.feed, Reader.remaining]
  rw [List.take_append_eq_append_take, List.take_of_length_le h]

/-- Fold a stream of input segments through the reader. -/
def runFeed (r : Reader) : List Bytes → Reader
  | [] => r
  | seg :: segs => runFeed (r.feed seg) segs

/-- `runFeed` preserves the invariant. -/
theorem runFeed_wf (r : Reader) (segs : List Bytes) (h : r.Wf) :
    (runFeed r segs).Wf := by
  induction segs generalizing r with
  | nil => simpa [runFeed] using h
  | cons seg segs ih => exact ih (r.feed seg) (feed_wf r seg h)

/-- `runFeed` never changes the `total`. -/
theorem runFeed_total (r : Reader) (segs : List Bytes) :
    (runFeed r segs).total = r.total := by
  induction segs generalizing r with
  | nil => rfl
  | cons seg segs ih => simpa [runFeed, Reader.feed] using ih (r.feed seg)

/-- Truncating an already-truncated prefix before re-appending is the same as
truncating the whole: `(X.take t ++ s).take t = (X ++ s).take t`. -/
theorem take_take_append (X s : Bytes) (t : Nat) :
    (X.take t ++ s).take t = (X ++ s).take t := by
  rcases Nat.le_total X.length t with hX | hX
  · rw [List.take_of_length_le hX]
  · rw [List.take_append_of_le_length (by rw [List.length_take]; omega),
        List.take_append_of_le_length hX, List.take_take]
    congr 1
    omega

/-- **Streaming fold delivers the prefix.** Folding a whole segment stream through
a fresh reader delivers exactly the length-`total` prefix of the concatenation of
the segments — the in-order body, with nothing reordered or dropped. -/
theorem runFeed_delivered (n : Nat) (segs : List Bytes) :
    (runFeed (Reader.init n) segs).delivered = segs.flatten.take n := by
  suffices h : ∀ (r : Reader), r.Wf →
      (runFeed r segs).delivered = (r.delivered ++ segs.flatten).take r.total by
    have := h (Reader.init n) (init_wf n)
    simpa [Reader.init] using this
  intro r hr
  induction segs generalizing r with
  | nil => simp [runFeed, List.take_of_length_le hr]
  | cons seg segs ih =>
    rw [runFeed, ih (r.feed seg) (feed_wf r seg hr),
        show (r.feed seg).total = r.total from rfl,
        feed_delivered r seg hr, take_take_append]
    simp [List.append_assoc]

/-- **Bytes conserved (theorem 1).** Once the input carries at least `total`
bytes, feeding it as a single segment to a fresh reader:

* reaches the terminal `complete` state;
* has delivered exactly `total` bytes;
* those bytes are precisely `input.take total` — the in-order length-`total`
  prefix of the input;
* the untouched tail `input.drop total` reassembles the input
  (`delivered ++ tail = input`), so nothing past `total` leaks into the body. -/
theorem complete_delivers_prefix (n : Nat) (input : Bytes) (h : n ≤ input.length) :
    ((Reader.init n).feed input).complete = true ∧
    ((Reader.init n).feed input).delivered = input.take n ∧
    ((Reader.init n).feed input).delivered.length = n ∧
    ((Reader.init n).feed input).delivered ++ input.drop n = input := by
  have hd : ((Reader.init n).feed input).delivered = input.take n := by
    rw [feed_delivered _ _ (init_wf n)]; simp [Reader.init]
  have ht : ((Reader.init n).feed input).total = n := rfl
  refine ⟨?_, hd, ?_, ?_⟩
  · simp only [Reader.complete, hd, ht, List.length_take, decide_eq_true_eq]; omega
  · rw [hd, List.length_take]; omega
  · rw [hd, List.take_append_drop]

/-- **Incomplete stays non-terminal (theorem 4).** A stream shorter than `total`
never reaches the terminal `complete` state: the reader does not falsely report
completion before `Content-Length` bytes have arrived. -/
theorem incomplete_not_complete (n : Nat) (input : Bytes) (h : input.length < n) :
    ((Reader.init n).feed input).complete = false := by
  have hd : ((Reader.init n).feed input).delivered = input.take n := by
    rw [feed_delivered _ _ (init_wf n)]; simp [Reader.init]
  have ht : ((Reader.init n).feed input).total = n := rfl
  simp only [Reader.complete, hd, ht, List.length_take, decide_eq_false_iff_not]
  omega

end ContentLength
end Body
