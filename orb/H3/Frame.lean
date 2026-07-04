import H3.Varint

/-!
# HTTP/3 frames (RFC 9114 §7)

Wire format of every frame: `[type varint][length varint][payload]`.

* `FrameType.ofNat` — the frame taxonomy (RFC 9114 §7.2), total on all 2^62
  type values: everything outside the known set maps to `unknown`.
* `decFrame` — the tri-state frame decoder
  (`complete / incomplete / error`, the package's uniform parse-step
  convention). Unknown frame types are **skipped, not rejected**
  (RFC 9114 §7.2.8: "implementations MUST ignore and discard any frame that
  has a type that is unknown") — `decFrame_unknown_skip`.
* **Totality + consumed-monotonicity**: `decFrame` is a total function into
  the tri-state (totality of the taxonomy is `decFrame_unknown_skip` +
  the known cases); `decFrame_consumed` proves `1 ≤ consumed ≤ input length`,
  which is exactly what makes the frame loop `decFrames` terminate — its
  acceptance by the termination checker is the operational form of the
  monotonicity theorem.
-/

namespace H3

/-- The frame taxonomy (RFC 9114 §7.2). `unknown` carries the raw type. -/
inductive FrameType where
  | data
  | headers
  | cancelPush
  | settings
  | pushPromise
  | goaway
  | maxPushId
  | unknown (t : Nat)
deriving Repr, DecidableEq

/-- Total classification of a decoded type varint. -/
def FrameType.ofNat (t : Nat) : FrameType :=
  if t = 0x00 then .data
  else if t = 0x01 then .headers
  else if t = 0x03 then .cancelPush
  else if t = 0x04 then .settings
  else if t = 0x05 then .pushPromise
  else if t = 0x07 then .goaway
  else if t = 0x0d then .maxPushId
  else .unknown t

/-- The known (structured) frame-type codes. -/
def isKnownType (t : Nat) : Bool :=
  t = 0x00 || t = 0x01 || t = 0x03 || t = 0x04 || t = 0x05 || t = 0x07 ||
    t = 0x0d

theorem FrameType.ofNat_unknown (t : Nat) (h : isKnownType t = false) :
    FrameType.ofNat t = .unknown t := by
  unfold isKnownType at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h3⟩, h4⟩, h5⟩, h7⟩, h13⟩ := h
  unfold FrameType.ofNat
  simp [h0, h1, h3, h4, h5, h7, h13]

/-- A decoded HTTP/3 frame. `unknown` retains only type and payload length —
the payload has been discarded (the skip rule). -/
inductive Frame where
  /-- DATA (0x00): request/response body bytes. -/
  | data (payload : Bytes)
  /-- HEADERS (0x01): a QPACK-encoded field section (see `H3.Qpack`). -/
  | headers (encoded : Bytes)
  /-- CANCEL_PUSH (0x03). -/
  | cancelPush (pushId : Nat)
  /-- SETTINGS (0x04): identifier/value varint pairs. -/
  | settings (pairs : List (Nat × Nat))
  /-- PUSH_PROMISE (0x05): push id + QPACK-encoded field section. -/
  | pushPromise (pushId : Nat) (encoded : Bytes)
  /-- GOAWAY (0x07). -/
  | goaway (streamId : Nat)
  /-- MAX_PUSH_ID (0x0d). -/
  | maxPushId (pushId : Nat)
  /-- Unknown/extension type: skipped per RFC 9114 §7.2.8. -/
  | unknown (frameType : Nat) (len : Nat)
deriving Repr, DecidableEq

/- The discriminant names below are used only by `decreasing_by`, which the
unused-variable linter cannot see. -/
set_option linter.unusedVariables false in
/-- SETTINGS payload (RFC 9114 §7.2.4): a sequence of identifier/value varint
pairs filling the whole payload. `none` on a truncated pair. Termination is
by `decVarint_consumed_pos`: every pair eats at least one byte. -/
def decSettings (bs : Bytes) : Option (List (Nat × Nat)) :=
  match bs with
  | [] => some []
  | b :: rest =>
    match h1 : Varint.decVarint (b :: rest) with
    | none => none
    | some (ident, n1) =>
      match Varint.decVarint ((b :: rest).drop n1) with
      | none => none
      | some (value, n2) =>
        match decSettings ((b :: rest).drop (n1 + n2)) with
        | none => none
        | some pairs => some ((ident, value) :: pairs)
termination_by bs.length
decreasing_by
  have := Varint.decVarint_consumed_pos _ _ _ h1
  simp only [List.length_drop, List.length_cons]
  omega

/-- Tri-state outcome of a frame parse step: the package's uniform
`complete / incomplete / error` convention. `error` means a *structured
payload* of a known frame type failed to parse; a truncated header or
payload is `incomplete` (more transport bytes can still complete it). -/
inductive FrameResult where
  | complete (frame : Frame) (consumed : Nat)
  | incomplete
  | error
deriving Repr, DecidableEq

/-- Decode one frame from the head of `bs`.

Header = type varint + length varint; then the payload must be fully present
(else `incomplete`); then the taxonomy dispatches. Unknown types yield
`.complete (.unknown t len)` consuming header + payload — the skip rule. -/
def decFrame (bs : Bytes) : FrameResult :=
  match Varint.decVarint bs with
  | none => .incomplete
  | some (t, n1) =>
    match Varint.decVarint (bs.drop n1) with
    | none => .incomplete
    | some (len, n2) =>
      let body := bs.drop (n1 + n2)
      if body.length < len then .incomplete
      else
        let payload := body.take len
        let consumed := n1 + n2 + len
        match FrameType.ofNat t with
        | .data => .complete (.data payload) consumed
        | .headers => .complete (.headers payload) consumed
        | .cancelPush =>
          match Varint.decVarint payload with
          | some (pushId, _) => .complete (.cancelPush pushId) consumed
          | none => .error
        | .settings =>
          match decSettings payload with
          | some pairs => .complete (.settings pairs) consumed
          | none => .error
        | .pushPromise =>
          match Varint.decVarint payload with
          | some (pushId, m) =>
            .complete (.pushPromise pushId (payload.drop m)) consumed
          | none => .error
        | .goaway =>
          match Varint.decVarint payload with
          | some (streamId, _) => .complete (.goaway streamId) consumed
          | none => .error
        | .maxPushId =>
          match Varint.decVarint payload with
          | some (pushId, _) => .complete (.maxPushId pushId) consumed
          | none => .error
        | .unknown t' => .complete (.unknown t' len) consumed

/-! ## Consumed-monotonicity -/

/-- **Consumed-monotonicity**: a completed frame consumes at least one byte
(progress — a frame loop strictly advances) and never more than the input
holds (boundedness — the decoder cannot over-read). -/
theorem decFrame_consumed (bs : Bytes) (f : Frame) (n : Nat)
    (h : decFrame bs = .complete f n) : 1 ≤ n ∧ n ≤ bs.length := by
  unfold decFrame at h
  split at h
  · exact absurd h (by simp)
  · rename_i t n1 h1
    split at h
    · exact absurd h (by simp)
    · rename_i len n2 h2
      have c1 := Varint.decVarint_consumed _ _ _ h1
      have c2 := Varint.decVarint_consumed _ _ _ h2
      simp only [List.length_drop] at c2
      simp only [] at h
      repeat' split at h
      all_goals cases h
      all_goals simp only [List.length_drop] at *
      all_goals omega

theorem decFrame_consumed_pos (bs : Bytes) (f : Frame) (n : Nat)
    (h : decFrame bs = .complete f n) : 1 ≤ n :=
  (decFrame_consumed bs f n h).1

theorem decFrame_consumed_le (bs : Bytes) (f : Frame) (n : Nat)
    (h : decFrame bs = .complete f n) : n ≤ bs.length :=
  (decFrame_consumed bs f n h).2

/-! ## The unknown-type skip rule -/

/-- **Unknown-type skip** (RFC 9114 §7.2.8): for *any* type value outside the
known set, a frame whose payload is fully present decodes to `.unknown` and
consumes header + payload exactly — no unknown type is ever rejected. With
the known-type cases of `decFrame` this makes the taxonomy total. -/
theorem decFrame_unknown_skip (t len : Nat) (tbs lbs payload tail : Bytes)
    (ht : Varint.encVarint t = some tbs) (hl : Varint.encVarint len = some lbs)
    (hunk : isKnownType t = false) (hp : payload.length = len) :
    decFrame (tbs ++ (lbs ++ (payload ++ tail))) =
      .complete (.unknown t len) (tbs.length + lbs.length + len) := by
  have hbs : List.drop (tbs.length + lbs.length)
      (tbs ++ (lbs ++ (payload ++ tail))) = payload ++ tail := by
    rw [← List.append_assoc, ← List.length_append, List.drop_left]
  unfold decFrame
  rw [Varint.decVarint_encVarint t tbs (lbs ++ (payload ++ tail)) ht]
  simp only [List.drop_left]
  rw [Varint.decVarint_encVarint len lbs (payload ++ tail) hl]
  simp only []
  rw [hbs, if_neg (by simp only [List.length_append, hp]; omega),
    FrameType.ofNat_unknown t hunk]

set_option linter.unusedVariables false in
/-- The frame loop: parse consecutive frames until `incomplete`/`error`,
returning the parsed frames and the unconsumed remainder. Its termination
proof *is* the consumed-monotonicity theorem in operational form. (The
discriminant name `h` is used only by `decreasing_by`.) -/
def decFrames (bs : Bytes) : List Frame × Bytes :=
  match h : decFrame bs with
  | .complete f n =>
    let r := decFrames (bs.drop n)
    (f :: r.1, r.2)
  | .incomplete => ([], bs)
  | .error => ([], bs)
termination_by bs.length
decreasing_by
  have := decFrame_consumed bs f n h
  simp only [List.length_drop]
  omega

/-! ## Wire vectors, checker-verified (the SETTINGS one goes through
`#guard` because well-founded definitions do not kernel-reduce) -/

example : decFrame [0x00, 0x03, 0xaa, 0xbb, 0xcc]
    = .complete (.data [0xaa, 0xbb, 0xcc]) 5 := rfl
example : decFrame [0x01, 0x02, 0xd1, 0xd7]
    = .complete (.headers [0xd1, 0xd7]) 4 := rfl
/-- Unknown type `0x21` with a 2-byte payload: skipped, not rejected. -/
example : decFrame [0x21, 0x02, 0xde, 0xad, 0x00]
    = .complete (.unknown 0x21 2) 4 := rfl
/-- Truncated payload: incomplete, not an error. -/
example : decFrame [0x01, 0x05, 0x01] = .incomplete := rfl
example : decFrame [] = .incomplete := rfl
#guard decFrame [0x04, 0x02, 0x01, 0x00] = .complete (.settings [(1, 0)]) 4

end H3
