/-
Captp.Frame — the wire-frame taxonomy and a total, consumed-monotone decoder.

A frame (`Frame`) is one capability-transport message: a delivery (expecting a
reply, or fire-and-forget), a subscription, an import/export-table GC
operation, or a connection abort.  Frames are the units the byte transport
carries; the session layer (`Captp.Session`) interprets a frame's descriptors
against its tables.

The decoder is written in an explicit suffix-passing reader monad
`Reader α := List Byte → Option (α × List Byte)`: a parse reads a prefix of the
input and returns the *unconsumed remainder*.  "Consumed-monotonicity" is then
the statement that the remainder is never longer than the input — the cursor
only moves forward — and, for a whole frame, strictly shorter (every frame
begins with a tag octet, so decoding always makes progress).  Progress is what
makes a frame *stream* decode terminate; `decodeStream` is defined by
well-founded recursion on exactly that decrease.

The encoding transcribed here is the reference TLV: a one-octet tag, then
fixed-width little-endian integers and length-prefixed byte strings.  Numeric
*values* are recovered by a total little-endian fold; two's-complement fidelity
of the signed GC weight and UTF-8 validation of string fields are out of scope
(the theorems below are value-agnostic — they constrain only how far the cursor
advances), and are named as scope cuts in CAPTP-NOTES.
-/
import Captp.Basic

namespace Captp

/-- One capability-transport wire message.

Mirrors the reference operation taxonomy: `Deliver` / `DeliverOnly` (the two
message-sends, with and without an answer position for pipelining), `Listen`
(subscribe to an answer/promise), `GcExport` / `GcAnswer` (the import/export
table GC operations), and `Abort`. -/
inductive Frame where
  | Deliver (target : Descriptor) (method : List Byte) (args : List Byte)
      (answerPos : Option Position)
  | DeliverOnly (target : Descriptor) (method : List Byte) (args : List Byte)
  | Listen (target : Position) (wantsPartial : Bool)
  | GcExport (exportPos : Position) (wireDelta : Int)
  | GcAnswer (answerPos : Position)
  | Abort (reason : List Byte)
deriving Repr

/-! ### The suffix-passing reader monad -/

/-- A parser: consume a prefix of the byte list, yield a value and the
unconsumed suffix, or fail. -/
abbrev Reader (α : Type) := List Byte → Option (α × List Byte)

namespace Reader

/-- Succeed without consuming input. -/
def pure' (a : α) : Reader α := fun s => some (a, s)

/-- Sequence two parses, threading the suffix. -/
def bind' (r : Reader α) (f : α → Reader β) : Reader β := fun s =>
  (r s).bind (fun p => f p.1 p.2)

/-- Always fail. -/
def fail : Reader α := fun _ => none

instance : Monad Reader where
  pure := pure'
  bind := bind'

theorem pure_eq (a : α) : (pure a : Reader α) = Reader.pure' a := rfl
theorem bind_eq (r : Reader α) (f : α → Reader β) : (r >>= f) = Reader.bind' r f := rfl

/-- Pop one octet. -/
def pop : Reader Byte := fun s =>
  match s with
  | [] => none
  | b :: rest => some (b, rest)

/-- Pop exactly `n` octets (fails if fewer remain). -/
def takeN : Nat → Reader (List Byte)
  | 0 => fun s => some ([], s)
  | n + 1 => fun s =>
      match s with
      | [] => none
      | b :: rest =>
          match takeN n rest with
          | none => none
          | some (bs, s') => some (b :: bs, s')

/-- Little-endian fold of octets to a natural number. -/
def leNat : List Byte → Nat
  | [] => 0
  | b :: bs => b + 256 * leNat bs

/-- A fixed 4-octet little-endian position/count. -/
def readU32 : Reader Position := do
  let bs ← takeN 4
  pure (leNat bs)

/-- A fixed 8-octet little-endian signed weight.  (Unsigned interpretation;
signedness is a value-only scope cut — see the module header.) -/
def readI64 : Reader Int := do
  let bs ← takeN 8
  pure (leNat bs : Int)

/-- One boolean octet. -/
def readBool : Reader Bool := do
  let b ← pop
  pure (b ≠ 0)

/-- An optional 4-octet position, prefixed by a presence octet. -/
def readOptU32 : Reader (Option Position) := do
  let present ← readBool
  match present with
  | true => (do let p ← readU32; pure (some p))
  | false => pure none

/-- A length-prefixed byte string: a `u32` length then that many octets. -/
def readBytes : Reader (List Byte) := do
  let n ← readU32
  takeN n

end Reader

open Reader

/-! ### Descriptor and frame decoders -/

/-- Descriptor tag octets (reference TLV). -/
def descTag.importObject : Byte := 0x10
def descTag.importPromise : Byte := 0x11
def descTag.export : Byte := 0x12
def descTag.answer : Byte := 0x13
def descTag.handoffGive : Byte := 0x14
def descTag.handoffReceive : Byte := 0x15

/-- The field-reading body for a descriptor, given its already-consumed tag.
Total: an unknown tag fails. -/
def descBody (tag : Byte) : Reader Descriptor :=
  if tag = descTag.importObject then (do let p ← readU32; pure (Descriptor.ImportObject p))
  else if tag = descTag.importPromise then (do let p ← readU32; pure (Descriptor.ImportPromise p))
  else if tag = descTag.export then (do let p ← readU32; pure (Descriptor.Export p))
  else if tag = descTag.answer then (do let p ← readU32; pure (Descriptor.Answer p))
  else if tag = descTag.handoffGive then
    (do let k ← readBytes; let loc ← readBytes; let sess ← readBytes;
        pure (Descriptor.HandoffGive k loc sess))
  else if tag = descTag.handoffReceive then
    (do let rs ← readBytes; let side ← readBytes;
        pure (Descriptor.HandoffReceive rs side))
  else Reader.fail

/-- Decode a descriptor: tag octet then its fields. -/
def readDescriptor : Reader Descriptor := do
  let tag ← pop
  descBody tag

/-- Frame tag octets (reference TLV). -/
def frameTag.deliver : Byte := 0x01
def frameTag.deliverOnly : Byte := 0x02
def frameTag.listen : Byte := 0x03
def frameTag.gcExport : Byte := 0x04
def frameTag.gcAnswer : Byte := 0x05
def frameTag.abort : Byte := 0x06

/-- Field-reading body for a frame, given its already-consumed tag.  Total. -/
def frameBody (tag : Byte) : Reader Frame :=
  if tag = frameTag.deliver then
    (do let t ← readDescriptor; let m ← readBytes; let a ← readBytes; let ap ← readOptU32;
        pure (Frame.Deliver t m a ap))
  else if tag = frameTag.deliverOnly then
    (do let t ← readDescriptor; let m ← readBytes; let a ← readBytes;
        pure (Frame.DeliverOnly t m a))
  else if tag = frameTag.listen then
    (do let t ← readU32; let w ← readBool; pure (Frame.Listen t w))
  else if tag = frameTag.gcExport then
    (do let p ← readU32; let d ← readI64; pure (Frame.GcExport p d))
  else if tag = frameTag.gcAnswer then
    (do let p ← readU32; pure (Frame.GcAnswer p))
  else if tag = frameTag.abort then
    (do let r ← readBytes; pure (Frame.Abort r))
  else Reader.fail

/-- Decode one frame: tag octet then its fields.  Total on every input. -/
def decodeFrame : Reader Frame := do
  let tag ← pop
  frameBody tag

/-! ### Consumed-monotonicity

`Shrinks` = the cursor never moves backward (remainder no longer than input).
`Consumes` = the cursor strictly advances (remainder strictly shorter).  Both
are closed under `bind`, which is the whole content of "each read only advances
the cursor": a sequence of reads advances by the sum of the parts. -/

/-- The reader never lengthens its remainder. -/
def Shrinks (r : Reader α) : Prop :=
  ∀ s a s', r s = some (a, s') → s'.length ≤ s.length

/-- The reader strictly shortens its remainder (makes progress). -/
def Consumes (r : Reader α) : Prop :=
  ∀ s a s', r s = some (a, s') → s'.length < s.length

theorem Consumes.toShrinks {r : Reader α} (h : Consumes r) : Shrinks r :=
  fun s a s' hh => Nat.le_of_lt (h s a s' hh)

theorem Shrinks.pure (a : α) : Shrinks (pure a : Reader α) := by
  intro s a' s' hh
  simp only [Reader.pure_eq, Reader.pure', Option.some.injEq, Prod.mk.injEq] at hh
  obtain ⟨-, rfl⟩ := hh
  exact Nat.le_refl _

theorem Shrinks.fail : Shrinks (Reader.fail : Reader α) := by
  intro s a s' hh
  exact absurd hh (by simp [Reader.fail])

theorem Consumes.pop : Consumes Reader.pop := by
  intro s b s' hh
  cases s with
  | nil => exact absurd hh (by simp [Reader.pop])
  | cons c rest =>
    simp only [Reader.pop, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨-, rfl⟩ := hh
    simp only [List.length_cons]; omega

/-- `bind` preserves `Shrinks`: reading `r` then `f` advances by the sum. -/
theorem Shrinks.bind {r : Reader α} {f : α → Reader β}
    (hr : Shrinks r) (hf : ∀ a, Shrinks (f a)) : Shrinks (r >>= f) := by
  intro s b s' hh
  simp only [Reader.bind_eq, Reader.bind'] at hh
  cases hrs : r s with
  | none => rw [hrs] at hh; simp at hh
  | some p =>
    obtain ⟨a, s₁⟩ := p
    rw [hrs] at hh
    simp only [Option.bind] at hh
    exact Nat.le_trans (hf a s₁ b s' hh) (hr s a s₁ hrs)

/-- `bind` with a strictly-consuming first read strictly consumes overall. -/
theorem Consumes.bind_left {r : Reader α} {f : α → Reader β}
    (hr : Consumes r) (hf : ∀ a, Shrinks (f a)) : Consumes (r >>= f) := by
  intro s b s' hh
  simp only [Reader.bind_eq, Reader.bind'] at hh
  cases hrs : r s with
  | none => rw [hrs] at hh; simp at hh
  | some p =>
    obtain ⟨a, s₁⟩ := p
    rw [hrs] at hh
    simp only [Option.bind] at hh
    exact Nat.lt_of_le_of_lt (hf a s₁ b s' hh) (hr s a s₁ hrs)

/-- Exact-consumption of `takeN`: on success the remainder is shorter by `n`. -/
theorem takeN_exact (n : Nat) :
    ∀ s bs s', Reader.takeN n s = some (bs, s') → s'.length + n = s.length := by
  induction n with
  | zero =>
    intro s bs s' hh
    simp only [Reader.takeN, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨-, rfl⟩ := hh
    omega
  | succ n ih =>
    intro s bs s' hh
    cases s with
    | nil => simp only [Reader.takeN] at hh; exact Option.noConfusion hh
    | cons c rest =>
      simp only [Reader.takeN] at hh
      cases htn : Reader.takeN n rest with
      | none => rw [htn] at hh; exact Option.noConfusion hh
      | some q =>
        obtain ⟨bs₁, s₁⟩ := q
        rw [htn] at hh
        simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        have := ih rest bs₁ s₁ htn
        simp only [List.length_cons]; omega

theorem Shrinks.takeN (n : Nat) : Shrinks (Reader.takeN n) := by
  intro s bs s' hh
  have := takeN_exact n s bs s' hh
  omega

theorem Shrinks.readU32 : Shrinks Reader.readU32 :=
  Shrinks.bind (Shrinks.takeN 4) (fun _ => Shrinks.pure _)

theorem Shrinks.readI64 : Shrinks Reader.readI64 :=
  Shrinks.bind (Shrinks.takeN 8) (fun _ => Shrinks.pure _)

theorem Shrinks.readBool : Shrinks Reader.readBool :=
  Shrinks.bind Consumes.pop.toShrinks (fun _ => Shrinks.pure _)

theorem Shrinks.readOptU32 : Shrinks Reader.readOptU32 := by
  apply Shrinks.bind Shrinks.readBool
  intro b
  cases b with
  | false => exact Shrinks.pure _
  | true => exact Shrinks.bind Shrinks.readU32 (fun _ => Shrinks.pure _)

theorem Shrinks.readBytes : Shrinks Reader.readBytes :=
  Shrinks.bind Shrinks.readU32 (fun _ => Shrinks.takeN _)

/-- Every descriptor field-body shrinks (whatever the tag). -/
theorem descBody_shrinks (tag : Byte) : Shrinks (descBody tag) := by
  unfold descBody
  repeat' split
  all_goals first
    | exact Shrinks.bind Shrinks.readU32 (fun _ => Shrinks.pure _)
    | exact Shrinks.bind Shrinks.readBytes (fun _ =>
        Shrinks.bind Shrinks.readBytes (fun _ =>
          Shrinks.bind Shrinks.readBytes (fun _ => Shrinks.pure _)))
    | exact Shrinks.bind Shrinks.readBytes (fun _ =>
        Shrinks.bind Shrinks.readBytes (fun _ => Shrinks.pure _))
    | exact Shrinks.fail

/-- **A descriptor decode always consumes at least its tag octet.** -/
theorem Consumes.readDescriptor : Consumes readDescriptor :=
  Consumes.bind_left Consumes.pop descBody_shrinks

/-- Every frame field-body shrinks (whatever the tag). -/
theorem frameBody_shrinks (tag : Byte) : Shrinks (frameBody tag) := by
  unfold frameBody
  repeat' split
  all_goals first
    | exact Shrinks.bind Consumes.readDescriptor.toShrinks (fun _ =>
        Shrinks.bind Shrinks.readBytes (fun _ =>
          Shrinks.bind Shrinks.readBytes (fun _ =>
            Shrinks.bind Shrinks.readOptU32 (fun _ => Shrinks.pure _))))
    | exact Shrinks.bind Consumes.readDescriptor.toShrinks (fun _ =>
        Shrinks.bind Shrinks.readBytes (fun _ =>
          Shrinks.bind Shrinks.readBytes (fun _ => Shrinks.pure _)))
    | exact Shrinks.bind Shrinks.readU32 (fun _ =>
        Shrinks.bind Shrinks.readBool (fun _ => Shrinks.pure _))
    | exact Shrinks.bind Shrinks.readU32 (fun _ =>
        Shrinks.bind Shrinks.readI64 (fun _ => Shrinks.pure _))
    | exact Shrinks.bind Shrinks.readU32 (fun _ => Shrinks.pure _)
    | exact Shrinks.bind Shrinks.readBytes (fun _ => Shrinks.pure _)
    | exact Shrinks.fail

/-- **Consumed-monotonicity (headline).** Decoding one frame strictly advances
the cursor: the unconsumed remainder is strictly shorter than the input.  Total
and unconditional. -/
theorem decodeFrame_consumes : Consumes decodeFrame :=
  Consumes.bind_left Consumes.pop frameBody_shrinks

/-- The cursor never runs past the end: the remainder is no longer than the
input (consumed count is well-defined, never negative). -/
theorem decodeFrame_shrinks : Shrinks decodeFrame :=
  decodeFrame_consumes.toShrinks

/-- Bytes consumed by a successful parse. -/
def consumed (s s' : List Byte) : Nat := s.length - s'.length

/-- Every successful frame decode consumes at least one octet. -/
theorem decodeFrame_consumed_pos {s : List Byte} {f : Frame} {s' : List Byte}
    (h : decodeFrame s = some (f, s')) : 0 < consumed s s' := by
  have := decodeFrame_consumes s f s' h
  unfold consumed
  omega

/-! ### Stream monotonicity

Decoding successive frames advances the cursor monotonically; each frame
strictly.  `decodeStream` decodes greedily until the input is exhausted or a
frame fails, and it terminates precisely because each frame strictly consumes
(the well-founded measure is the remaining length). -/

/-- Two consecutive frame decodes advance the cursor strictly at each step and
monotonically overall. -/
theorem decode_two_monotone {s s₁ s₂ : List Byte} {f₁ f₂ : Frame}
    (h1 : decodeFrame s = some (f₁, s₁)) (h2 : decodeFrame s₁ = some (f₂, s₂)) :
    s₂.length < s₁.length ∧ s₁.length < s.length ∧ s₂.length < s.length := by
  have a := decodeFrame_consumes s f₁ s₁ h1
  have b := decodeFrame_consumes s₁ f₂ s₂ h2
  exact ⟨b, a, Nat.lt_trans b a⟩

/-- Greedy stream decode: decode frames until a frame fails (in particular when
the input is empty, since `decodeFrame [] = none`).  Terminates by the strict
decrease of the remaining length — the recursion is *justified by*
consumed-monotonicity. -/
def decodeStream (s : List Byte) : List Frame :=
  match hd : decodeFrame s with
  | none => []
  | some (f, s') =>
      have : s'.length < s.length := decodeFrame_consumes s f s' hd
      f :: decodeStream s'
termination_by s.length

end Captp
