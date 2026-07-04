import Dns.Basic

/-!
# Domain-name decoding with compression pointers (RFC 1035 §4.1.4)

A domain name on the wire is a sequence of labels. Each label begins with a
length octet whose top two bits select its kind:

| top 2 bits | meaning                                                        |
|------------|----------------------------------------------------------------|
| `00`       | a normal label; low 6 bits are its length `L` (`0..63`)        |
| `11`       | a compression pointer; low 14 bits are an offset into the msg  |
| `01`,`10`  | reserved                                                       |

A length octet of `0` (a normal label of length 0) is the root and terminates
the name. A pointer redirects decoding to an earlier point in the message so a
shared suffix need only appear once.

## The termination guarantee

Pointers can point anywhere, including at themselves, so adversarial input can
describe an infinite loop. The decoder must still terminate. We split the work:

* `readRun` reads a *run* of normal labels forward from an offset, stopping at
  the first root octet (→ `complete`) or the first pointer (→ `jump target`).
  It is structurally recursive on an explicit fuel seeded from the message
  length, so it is total with no side conditions.

* `followChain` resolves a pointer chain. It calls `readRun`; on a `jump` to
  `target` it recurses **only if `target < start`** — a pointer may jump only
  strictly backward, before the offset where the current run began. The
  recursion is well-founded on `start : Nat`: each followed jump strictly
  decreases it, and it is bounded below by `0`. A pointer that does not go
  strictly backward is rejected with `loopPointer`. This is the whole point:
  no adversarial pointer arrangement can make decoding diverge.

The "strictly backward" rule is conservative but sound: a well-formed compressor
only ever points to a name that already appeared *earlier* in the message, i.e.
at an offset below the current name's start.
-/

namespace Dns

/-- The `L` bytes of a label whose length octet sits at offset `i`. -/
def labelAt (msg : Bytes) (i L : Nat) : List UInt8 := (msg.drop (i + 1)).take L

/-- When the message holds the label, `labelAt` has length exactly `L`. -/
theorem labelAt_len (msg : Bytes) (i L : Nat) (h : i + 1 + L ≤ msg.length) :
    (labelAt msg i L).length = L := by
  unfold labelAt; rw [List.length_take, List.length_drop]; omega

/-- A length octet with top bits `00` (i.e. `b / 64 = 0`) encodes a length
`< 64`. -/
theorem hi_zero_lt (b : UInt8) (h : b.toNat / 64 = 0) : b.toNat < 64 := by omega

/-- The result of reading one forward run of labels. -/
inductive RunResult where
  /-- Reached the root octet; `endOff` is the offset just past it. -/
  | complete (labels : List (List UInt8)) (endOff : Nat)
  /-- Hit a compression pointer to `target`; `endOff` is the offset just past
  the two pointer octets. -/
  | jump (target : Nat) (labels : List (List UInt8)) (endOff : Nat)
  | error (e : ParseError)
  deriving Repr, DecidableEq

/-- Read a forward run of normal labels from offset `i`, appending to `acc`.
Stops at the first root octet or the first pointer. `fuel` bounds the number of
labels; callers seed it from the message length, which always suffices because
each label advances `i` by at least two. -/
def readRun (msg : Bytes) : Nat → List (List UInt8) → Nat → RunResult
  | _, _, 0 => .error .fuelExhausted
  | i, acc, Nat.succ fuel =>
    match msg[i]? with
    | none => .error .truncated
    | some b =>
      if b.toNat / 64 = 0 then
        if b.toNat = 0 then
          .complete acc (i + 1)
        else
          if i + 1 + b.toNat ≤ msg.length then
            if wireLen (acc ++ [labelAt msg i b.toNat]) ≤ maxName then
              readRun msg (i + 1 + b.toNat) (acc ++ [labelAt msg i b.toNat]) fuel
            else .error .nameTooLong
          else .error .truncated
      else if b.toNat / 64 = 3 then
        match msg[i + 1]? with
        | none => .error .truncated
        | some b2 => .jump ((b.toNat % 64) * 256 + b2.toNat) acc (i + 2)
      else .error .reservedLabel

/-- The result of resolving a full pointer chain. -/
inductive ChainResult where
  | okName (labels : List (List UInt8))
  | err (e : ParseError)
  deriving Repr, DecidableEq

/-- Resolve a pointer chain starting a run at offset `start` with labels so far
`acc`. Follows a pointer only when it jumps strictly backward (`target < start`);
otherwise fails with `loopPointer`. Well-founded on `start`. -/
def followChain (msg : Bytes) (start : Nat) (acc : List (List UInt8)) : ChainResult :=
  match readRun msg start acc (msg.length + 1) with
  | .error e => .err e
  | .complete o _ => .okName o
  | .jump t o _ =>
    if hlt : t < start then followChain msg t o
    else .err .loopPointer
termination_by start
decreasing_by exact hlt

/-- A fully decoded name plus the number of octets it occupied in its record.
`consumed` is measured over the *first* run only: a name inside a record ends
at its first pointer (or its root octet), and that is what advances the record
cursor. -/
structure Decoded where
  labels : List (List UInt8)
  consumed : Nat
  deriving Repr, DecidableEq

inductive NameResult where
  | ok (d : Decoded)
  | error (e : ParseError)
  deriving Repr, DecidableEq

/-- Decode a domain name starting at `start`. Total on every input. -/
def decodeName (msg : Bytes) (start : Nat) : NameResult :=
  match readRun msg start [] (msg.length + 1) with
  | .error e => .error e
  | .complete o endOff => .ok ⟨o, endOff - start⟩
  | .jump t o endOff =>
    match followChain msg t o with
    | .okName final => .ok ⟨final, endOff - start⟩
    | .err e => .error e

/-! ## Totality

Both recursive definitions are ordinary Lean `def`s: no `partial`, no `sorry`.
The kernel accepted `readRun` (structural on fuel) and `followChain`
(well-founded on `start`), so each denotes a total function — it returns a
value on every input, adversarial pointer loops included. -/

theorem readRun_total (msg : Bytes) (i : Nat) (acc : List (List UInt8)) (fuel : Nat) :
    ∃ r, readRun msg i acc fuel = r := ⟨_, rfl⟩

theorem followChain_total (msg : Bytes) (start : Nat) (acc : List (List UInt8)) :
    ∃ r, followChain msg start acc = r := ⟨_, rfl⟩

/-- **The anti-loop property.** `decodeName` returns a value on every input —
there is no input, adversarial or otherwise, on which it fails to terminate. -/
theorem decodeName_total (msg : Bytes) (start : Nat) :
    ∃ r, decodeName msg start = r := ⟨_, rfl⟩

/-! ## `followChain` unfolding lemmas -/

/-- One-step unfolding at a run that terminates without a pointer. -/
theorem followChain_complete (msg : Bytes) (start : Nat) (acc o : List (List UInt8))
    (e : Nat) (h : readRun msg start acc (msg.length + 1) = .complete o e) :
    followChain msg start acc = .okName o := by
  rw [followChain, h]

/-- One-step unfolding of `followChain` at a pointer that jumps strictly
backward: the chain continues at the target. -/
theorem followChain_follow (msg : Bytes) (start t : Nat)
    (acc o : List (List UInt8)) (e : Nat)
    (h : readRun msg start acc (msg.length + 1) = .jump t o e) (hlt : t < start) :
    followChain msg start acc = followChain msg t o := by
  rw [followChain, h]; simp only [hlt, dif_pos]

/-- **Strictly-backward guard.** A pointer that does not jump strictly backward
(`start ≤ target`) is rejected with `loopPointer`; it is never followed. This is
the invariant that forbids a pointer from re-entering the current run or
advancing into forward bytes. -/
theorem followChain_forward_rejected (msg : Bytes) (start t : Nat)
    (acc o : List (List UInt8)) (e : Nat)
    (h : readRun msg start acc (msg.length + 1) = .jump t o e) (hge : start ≤ t) :
    followChain msg start acc = .err .loopPointer := by
  rw [followChain, h]
  have hnot : ¬ t < start := by omega
  simp only [hnot, dif_neg, not_false_iff]

/-- A self-pointer (target equal to the run start) is a loop and is rejected. -/
theorem followChain_self_loop (msg : Bytes) (start : Nat)
    (acc o : List (List UInt8)) (e : Nat)
    (h : readRun msg start acc (msg.length + 1) = .jump start o e) :
    followChain msg start acc = .err .loopPointer :=
  followChain_forward_rejected msg start start acc o e h (Nat.le_refl start)

/-! ## The forward reader advances (consumed ≥ 1) -/

/-- Every `readRun` outcome reports an `endOff` at least one past the offset it
started at: the reader always consumes the length octet it inspected. -/
theorem readRun_endOff_ge (msg : Bytes) (i : Nat) (acc : List (List UInt8))
    (fuel : Nat) :
    (∀ o e, readRun msg i acc fuel = .complete o e → i + 1 ≤ e) ∧
    (∀ t o e, readRun msg i acc fuel = .jump t o e → i + 1 ≤ e) := by
  induction fuel generalizing i acc with
  | zero => constructor <;> intro <;> simp [readRun] at *
  | succ fuel ih =>
    constructor
    · intro o e h
      unfold readRun at h
      split at h
      · exact absurd h (by simp)
      · rename_i b hb
        split at h
        · split at h
          · injection h with ho he; omega
          · split at h
            · split at h
              · have := (ih (i + 1 + b.toNat) _).1 o e h; omega
              · exact absurd h (by simp)
            · exact absurd h (by simp)
        · split at h
          · split at h
            · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
    · intro t o e h
      unfold readRun at h
      split at h
      · exact absurd h (by simp)
      · rename_i b hb
        split at h
        · split at h
          · exact absurd h (by simp)
          · split at h
            · split at h
              · have := (ih (i + 1 + b.toNat) _).2 t o e h; omega
              · exact absurd h (by simp)
            · exact absurd h (by simp)
        · split at h
          · split at h
            · exact absurd h (by simp)
            · injection h with ht ho he; omega
          · exact absurd h (by simp)

/-- A successful name decode consumed at least one octet, so parsing a name
always advances the record cursor (`consumed`-monotone). -/
theorem decodeName_consumed_pos (msg : Bytes) (start : Nat) (d : Decoded)
    (h : decodeName msg start = .ok d) : 1 ≤ d.consumed := by
  unfold decodeName at h
  split at h
  · exact absurd h (by simp)
  · rename_i o e heq
    injection h with h; subst h
    have hb := (readRun_endOff_ge msg start [] (msg.length + 1)).1 o e heq
    dsimp only [Decoded.consumed]; omega
  · rename_i t o e heq
    split at h
    · rename_i final hfc
      injection h with h; subst h
      have hb := (readRun_endOff_ge msg start [] (msg.length + 1)).2 t o e heq
      dsimp only [Decoded.consumed]; omega
    · exact absurd h (by simp)

/-! ## Bounded name length (≤ 255 octets)

The cap check inside `readRun` rejects any label whose addition would push the
wire length past `maxName`. So a decoded name's wire length is `≤ 255`. -/

/-- `readRun` never grows the wire length past `maxName`. -/
theorem readRun_wireLen_le (msg : Bytes) (i : Nat) (acc : List (List UInt8))
    (fuel : Nat) (hacc : wireLen acc ≤ maxName) :
    (∀ o e, readRun msg i acc fuel = .complete o e → wireLen o ≤ maxName) ∧
    (∀ t o e, readRun msg i acc fuel = .jump t o e → wireLen o ≤ maxName) := by
  induction fuel generalizing i acc with
  | zero => constructor <;> intro <;> simp [readRun] at *
  | succ fuel ih =>
    constructor
    · intro o e h
      unfold readRun at h
      split at h
      · exact absurd h (by simp)
      · rename_i b hb
        split at h
        · split at h
          · injection h with ho he; subst ho; exact hacc
          · split at h
            · split at h
              · rename_i hcap
                exact (ih (i + 1 + b.toNat) _ hcap).1 o e h
              · exact absurd h (by simp)
            · exact absurd h (by simp)
        · split at h
          · split at h
            · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
    · intro t o e h
      unfold readRun at h
      split at h
      · exact absurd h (by simp)
      · rename_i b hb
        split at h
        · split at h
          · exact absurd h (by simp)
          · split at h
            · split at h
              · rename_i hcap
                exact (ih (i + 1 + b.toNat) _ hcap).2 t o e h
              · exact absurd h (by simp)
            · exact absurd h (by simp)
        · split at h
          · split at h
            · exact absurd h (by simp)
            · injection h with ht ho he; subst ho; exact hacc
          · exact absurd h (by simp)

/-- `followChain` preserves the wire-length bound along the whole pointer
chain. -/
theorem followChain_wireLen_le (msg : Bytes) (start : Nat)
    (acc : List (List UInt8)) (hacc : wireLen acc ≤ maxName) :
    ∀ o, followChain msg start acc = .okName o → wireLen o ≤ maxName := by
  induction start using Nat.strongRecOn generalizing acc with
  | ind start ih =>
    intro o h
    rw [followChain] at h
    split at h
    · exact absurd h (by simp)
    · rename_i out _ heq
      injection h with h; subst h
      exact (readRun_wireLen_le msg start acc (msg.length + 1) hacc).1 out _ heq
    · rename_i t out e heq
      split at h
      · rename_i hlt
        have hout : wireLen out ≤ maxName :=
          (readRun_wireLen_le msg start acc (msg.length + 1) hacc).2 t out e heq
        exact ih t hlt out hout o h
      · exact absurd h (by simp)

/-- **Bounded length.** A decoded name is at most `maxName` = 255 octets in
wire form (RFC 1035 §2.3.4). -/
theorem decodeName_wireLen_le (msg : Bytes) (start : Nat) (d : Decoded)
    (h : decodeName msg start = .ok d) : wireLen d.labels ≤ maxName := by
  have hnil : wireLen ([] : List (List UInt8)) ≤ maxName := by
    rw [wireLen_nil]; decide
  unfold decodeName at h
  split at h
  · exact absurd h (by simp)
  · rename_i o e heq
    injection h with h; subst h
    exact (readRun_wireLen_le msg start [] (msg.length + 1) hnil).1 o e heq
  · rename_i t o e heq
    split at h
    · rename_i final hfc
      injection h with h; subst h
      have hout : wireLen o ≤ maxName :=
        (readRun_wireLen_le msg start [] (msg.length + 1) hnil).2 t o e heq
      exact followChain_wireLen_le msg t o hout final hfc
    · exact absurd h (by simp)

/-! ## Label constraints (1 ≤ length ≤ 63)

Every label the reader emits comes from a length octet with top bits `00` and a
nonzero low 6 bits, so its length is in `1..63`. -/

/-- Every label has length in `1..maxLabel`. -/
def LabelsOk (ls : List (List UInt8)) : Prop :=
  ∀ lab ∈ ls, 1 ≤ lab.length ∧ lab.length ≤ maxLabel

theorem labelsOk_nil : LabelsOk [] := by intro _ h; simp at h

theorem labelsOk_append (ls : List (List UInt8)) (l : List UInt8)
    (hls : LabelsOk ls) (hl : 1 ≤ l.length ∧ l.length ≤ maxLabel) :
    LabelsOk (ls ++ [l]) := by
  intro lab hlab
  rcases List.mem_append.mp hlab with h | h
  · exact hls lab h
  · simp only [List.mem_singleton] at h; subst h; exact hl

/-- `readRun` only ever emits labels of length `1..63`. -/
theorem readRun_labelsOk (msg : Bytes) (i : Nat) (acc : List (List UInt8))
    (fuel : Nat) (hacc : LabelsOk acc) :
    (∀ o e, readRun msg i acc fuel = .complete o e → LabelsOk o) ∧
    (∀ t o e, readRun msg i acc fuel = .jump t o e → LabelsOk o) := by
  induction fuel generalizing i acc with
  | zero => constructor <;> intro <;> simp [readRun] at *
  | succ fuel ih =>
    constructor
    · intro o e h
      unfold readRun at h
      split at h
      · exact absurd h (by simp)
      · rename_i b hb
        split at h
        · rename_i hzero
          split at h
          · injection h with ho he; subst ho; exact hacc
          · split at h
            · rename_i hlen
              split at h
              · have hlablen := labelAt_len msg i b.toNat hlen
                have hb64 := hi_zero_lt b hzero
                have hok : 1 ≤ (labelAt msg i b.toNat).length ∧
                    (labelAt msg i b.toNat).length ≤ maxLabel := by
                  rw [hlablen]; unfold maxLabel; omega
                exact (ih (i + 1 + b.toNat) _
                  (labelsOk_append acc _ hacc hok)).1 o e h
              · exact absurd h (by simp)
            · exact absurd h (by simp)
        · split at h
          · split at h
            · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
    · intro t o e h
      unfold readRun at h
      split at h
      · exact absurd h (by simp)
      · rename_i b hb
        split at h
        · rename_i hzero
          split at h
          · exact absurd h (by simp)
          · split at h
            · rename_i hlen
              split at h
              · have hlablen := labelAt_len msg i b.toNat hlen
                have hb64 := hi_zero_lt b hzero
                have hok : 1 ≤ (labelAt msg i b.toNat).length ∧
                    (labelAt msg i b.toNat).length ≤ maxLabel := by
                  rw [hlablen]; unfold maxLabel; omega
                exact (ih (i + 1 + b.toNat) _
                  (labelsOk_append acc _ hacc hok)).2 t o e h
              · exact absurd h (by simp)
            · exact absurd h (by simp)
        · split at h
          · split at h
            · exact absurd h (by simp)
            · injection h with ht ho he; subst ho; exact hacc
          · exact absurd h (by simp)

theorem followChain_labelsOk (msg : Bytes) (start : Nat)
    (acc : List (List UInt8)) (hacc : LabelsOk acc) :
    ∀ o, followChain msg start acc = .okName o → LabelsOk o := by
  induction start using Nat.strongRecOn generalizing acc with
  | ind start ih =>
    intro o h
    rw [followChain] at h
    split at h
    · exact absurd h (by simp)
    · rename_i out _ heq
      injection h with h; subst h
      exact (readRun_labelsOk msg start acc (msg.length + 1) hacc).1 out _ heq
    · rename_i t out e heq
      split at h
      · rename_i hlt
        have hout : LabelsOk out :=
          (readRun_labelsOk msg start acc (msg.length + 1) hacc).2 t out e heq
        exact ih t hlt out hout o h
      · exact absurd h (by simp)

/-- **Label bound.** Every label of a decoded name has length `1..63`. -/
theorem decodeName_labelsOk (msg : Bytes) (start : Nat) (d : Decoded)
    (h : decodeName msg start = .ok d) : LabelsOk d.labels := by
  unfold decodeName at h
  split at h
  · exact absurd h (by simp)
  · rename_i o e heq
    injection h with h; subst h
    exact (readRun_labelsOk msg start [] (msg.length + 1) labelsOk_nil).1 o e heq
  · rename_i t o e heq
    split at h
    · rename_i final hfc
      injection h with h; subst h
      have hout : LabelsOk o :=
        (readRun_labelsOk msg start [] (msg.length + 1) labelsOk_nil).2 t o e heq
      exact followChain_labelsOk msg t o hout final hfc
    · exact absurd h (by simp)

/-! ## Worked wire vectors (RFC 1035), checker-verified

`readRun` is structural, so it reduces in the kernel; the uncompressed decode
reduces too because that path never touches `followChain`. The compressed and
adversarial vectors go through `followChain` (well-founded, so it does not
reduce by `rfl`) and are discharged with the unfolding lemmas above. -/

/-- `www.example.com`, uncompressed: three labels, root, 17 octets consumed. -/
example :
    decodeName
      [3, 119, 119, 119, 7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0] 0
      = .ok ⟨[[119, 119, 119], [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]], 17⟩ := by
  decide

/-- The wire length of that name is 17 ≤ 255. -/
example :
    wireLen [[119, 119, 119], [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]] = 17 := by
  decide

/-- A self-pointer at offset 0 (`C0 00` → target 0) is an adversarial loop; the
decoder terminates with `loopPointer` rather than diverging. -/
example : decodeName [0xC0, 0x00] 0 = .error .loopPointer := by
  have hr : readRun [0xC0, 0x00] 0 [] (([0xC0, 0x00] : Bytes).length + 1)
      = .jump 0 [] 2 := by decide
  have hf : followChain [0xC0, 0x00] 0 [] = .err .loopPointer :=
    followChain_self_loop [0xC0, 0x00] 0 [] [] 2 hr
  unfold decodeName
  rw [hr]; simp only [hf]

/-- A two-pointer cycle `0 → 2 → 0` also terminates with `loopPointer`. The hop
`2 → 0` is strictly backward and is followed; the hop `0 → 2` is forward and is
rejected, breaking the cycle. -/
example : decodeName [0xC0, 0x02, 0xC0, 0x00] 0 = .error .loopPointer := by
  have hr0 : readRun [0xC0, 0x02, 0xC0, 0x00] 0 []
      (([0xC0, 0x02, 0xC0, 0x00] : Bytes).length + 1) = .jump 2 [] 2 := by decide
  have hr2 : readRun [0xC0, 0x02, 0xC0, 0x00] 2 []
      (([0xC0, 0x02, 0xC0, 0x00] : Bytes).length + 1) = .jump 0 [] 4 := by decide
  have step : followChain [0xC0, 0x02, 0xC0, 0x00] 2 []
      = followChain [0xC0, 0x02, 0xC0, 0x00] 0 [] :=
    followChain_follow _ 2 0 [] [] 4 hr2 (by omega)
  have hf0 : followChain [0xC0, 0x02, 0xC0, 0x00] 0 [] = .err .loopPointer :=
    followChain_forward_rejected _ 0 2 [] [] 2 hr0 (by omega)
  unfold decodeName
  rw [hr0]; simp only [step, hf0]

/-- A compressed name: `www` then a pointer back to `example.com` at offset 0.
Decoding follows the (backward) pointer and terminates with the full name;
6 octets were consumed in the record (3-byte label + 1 length octet + 2 pointer
octets). -/
example :
    decodeName
      [7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0,
       3, 119, 119, 119, 0xC0, 0x00] 13
      = .ok ⟨[[119, 119, 119], [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]], 6⟩ := by
  have hr13 : readRun
      [7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0,
       3, 119, 119, 119, 0xC0, 0x00] 13 []
      (([7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0,
         3, 119, 119, 119, 0xC0, 0x00] : Bytes).length + 1)
      = .jump 0 [[119, 119, 119]] 19 := by decide
  have hr0 : readRun
      [7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0,
       3, 119, 119, 119, 0xC0, 0x00] 0 [[119, 119, 119]]
      (([7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0,
         3, 119, 119, 119, 0xC0, 0x00] : Bytes).length + 1)
      = .complete [[119, 119, 119], [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]] 13 := by
    decide
  have hfc : followChain
      [7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0,
       3, 119, 119, 119, 0xC0, 0x00] 0 [[119, 119, 119]]
      = .okName [[119, 119, 119], [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]] :=
    followChain_complete _ 0 _ _ 13 hr0
  unfold decodeName
  rw [hr13]; simp only [hfc]

end Dns
