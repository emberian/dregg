/-
Token — the 64-bit completion-token partition.

A completion-queue reactor multiplexes every in-flight operation through one
64-bit token word (io_uring's `user_data`) carried from submission to
completion. The word must disambiguate, in a single flat space:

  * the wakeup sentinel (`0`) — the multishot poll on the reactor's wakeup fd;
  * the cancel sentinel (all ones) — async-cancel submissions;
  * pending-operation slab keys — slot index in the low 32 bits, slot-reuse
    generation in the high 32 bits;
  * multishot-accept tags — top 16 bits `0xACCE`, listener fd in the low 32;
  * multishot-recv tags — top 16 bits `0xBECF`, socket fd in the low 32;
  * multishot-recvmsg (UDP) tags — top 16 bits `0xDC4F`, socket fd low 32;
  * cross-queue messages — top byte `0xFF`, opcode/source/payload fields;
  * cross-queue send confirmations — exactly `0xFE <<< 56`;
  * per-channel wakeups — top byte `0xCA`, channel id in the low 8 bits;
  * periodic-timer tokens — bit 63 set, job id in the low bits.

A misrouted completion is the fd-reuse ABA's ugly sibling: a completion for
one object dispatched as if it belonged to another. The theorem that forbids
it is `decode_encode` (decode is a retraction of encode on well-formed
tokens), with injectivity of `encode` as a corollary.

Two well-formedness side conditions are load-bearing and easy to miss:

  1. `generation < 2^31` on slab keys. The tagged namespaces all live in the
     bit-63 half of the space, so a slab key stays disjoint from every tag
     exactly when its generation keeps the top bit clear. A free-running
     32-bit generation counter violates this: see
     `slab_generation_overflow_collides` for a concrete collision.
  2. The all-ones corner of the message-ring namespace IS the cancel
     sentinel: see `msgRing_corner_aliases_cancel`. Well-formedness excludes
     that single point.

`decode` is written as the dispatch priority chain (sentinels first, then
top-byte markers, then top-16-bit tags, then bit 63, slab keys as the
residue), mirroring how a completion loop routes a token.

All arithmetic is carried out in `Nat`; `encode_lt_tokenSpace` confirms every
well-formed token fits in 64 bits.
-/

namespace Flow

/-- `2^64` — the size of the completion-token word. -/
def tokenSpace : Nat := 2 ^ 64

/-- The completion-token namespaces, as a datatype. One constructor per
namespace; the payloads are the fields recovered on dispatch. -/
inductive Token where
  /-- Wakeup sentinel: the multishot poll on the reactor's wakeup fd.
  Encodes to `0`. -/
  | wakeup
  /-- Cancel sentinel for async-cancel submissions. Encodes to `2^64 - 1`. -/
  | cancel
  /-- A pending-operation slab key: slot `index` in the low 32 bits, the
  slot-reuse `generation` in the high 32 bits. Slot 0 is reserved (key `0`
  would collide with the wakeup sentinel), and the generation must stay
  below `2^31` to keep slab keys out of the tagged half of the space. -/
  | slab (index generation : Nat)
  /-- Multishot-accept tag: top 16 bits `0xACCE`, listener fd in the low
  32 bits. -/
  | acceptMulti (listenerFd : Nat)
  /-- Multishot-recv tag: top 16 bits `0xBECF`, socket fd in the low
  32 bits. -/
  | recvMulti (socketFd : Nat)
  /-- Multishot-recvmsg (UDP) tag: top 16 bits `0xDC4F`, socket fd in the
  low 32 bits. -/
  | recvMsgMulti (socketFd : Nat)
  /-- A cross-queue message: top byte `0xFF`, opcode in bits 55–48, source
  reactor id in bits 47–32, payload in the low 32 bits. -/
  | msgRing (opcode source payload : Nat)
  /-- Source-side confirmation of a cross-queue message: exactly
  `0xFE <<< 56`. -/
  | msgRingSent
  /-- Per-channel wakeup: top byte `0xCA`, channel id in the low 8 bits. -/
  | channel (id : Nat)
  /-- Periodic-timer token: bit 63 set, job id in the low bits. The job id
  is bounded by `2^48` so the token cannot wander into the tag windows. -/
  | timer (job : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace Token

/-- Field bounds per namespace. Every bound is decidable; `decide` closes
concrete instances. -/
def Wf : Token → Prop
  | .wakeup => True
  | .cancel => True
  | .slab index generation => 0 < index ∧ index < 2 ^ 32 ∧ generation < 2 ^ 31
  | .acceptMulti fd => fd < 2 ^ 32
  | .recvMulti fd => fd < 2 ^ 32
  | .recvMsgMulti fd => fd < 2 ^ 32
  | .msgRing opcode source payload =>
      opcode < 2 ^ 8 ∧ source < 2 ^ 16 ∧ payload < 2 ^ 32 ∧
      ¬(opcode = 0xFF ∧ source = 0xFFFF ∧ payload = 2 ^ 32 - 1)
  | .msgRingSent => True
  | .channel id => id < 2 ^ 8
  | .timer job => job < 2 ^ 48

instance (t : Token) : Decidable t.Wf := by
  cases t <;> (simp only [Wf]; infer_instance)

/-- Encode a token into the 64-bit word. -/
def encode : Token → Nat
  | .wakeup => 0
  | .cancel => 2 ^ 64 - 1
  | .slab index generation => generation * 2 ^ 32 + index
  | .acceptMulti fd => 0xACCE * 2 ^ 48 + fd
  | .recvMulti fd => 0xBECF * 2 ^ 48 + fd
  | .recvMsgMulti fd => 0xDC4F * 2 ^ 48 + fd
  | .msgRing opcode source payload =>
      0xFF * 2 ^ 56 + opcode * 2 ^ 48 + source * 2 ^ 32 + payload
  | .msgRingSent => 0xFE * 2 ^ 56
  | .channel id => 0xCA * 2 ^ 56 + id
  | .timer job => 2 ^ 63 + job

/-- Decode a 64-bit word, in dispatch priority order: sentinels, top-byte
markers, top-16-bit tags, the bit-63 timer namespace, and slab keys as the
residue. Total — junk words decode to *something*; the round-trip theorem
holds on well-formed tokens. -/
def decode (v : Nat) : Option Token :=
  if v = 0 then some .wakeup
  else if v = 2 ^ 64 - 1 then some .cancel
  else if v / 2 ^ 56 = 0xCA then some (.channel (v % 2 ^ 8))
  else if v / 2 ^ 56 = 0xFE then some .msgRingSent
  else if v / 2 ^ 56 = 0xFF then
    some (.msgRing (v / 2 ^ 48 % 2 ^ 8) (v / 2 ^ 32 % 2 ^ 16) (v % 2 ^ 32))
  else if v / 2 ^ 48 = 0xACCE then some (.acceptMulti (v % 2 ^ 32))
  else if v / 2 ^ 48 = 0xBECF then some (.recvMulti (v % 2 ^ 32))
  else if v / 2 ^ 48 = 0xDC4F then some (.recvMsgMulti (v % 2 ^ 32))
  else if 2 ^ 63 ≤ v then some (.timer (v % 2 ^ 63))
  else some (.slab (v % 2 ^ 32) (v / 2 ^ 32))

/-- Every well-formed token fits in the 64-bit word. -/
theorem encode_lt_tokenSpace (t : Token) (h : t.Wf) : t.encode < tokenSpace := by
  cases t <;> simp only [Wf] at h <;> simp only [encode, tokenSpace] <;> omega

/-- **The partition theorem.** Decoding is a retraction of encoding on
well-formed tokens: every namespace is recovered, with its fields, from the
bare 64-bit word. -/
theorem decode_encode (t : Token) (h : t.Wf) : decode t.encode = some t := by
  cases t with
  | wakeup => decide
  | cancel => decide
  | slab index generation =>
    obtain ⟨h1, h2, h3⟩ := h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg]
    · simp only [Option.some.injEq, Token.slab.injEq]
      omega
    all_goals omega
  | acceptMulti fd =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.acceptMulti.injEq]
      omega
    all_goals omega
  | recvMulti fd =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.recvMulti.injEq]
      omega
    all_goals omega
  | recvMsgMulti fd =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.recvMsgMulti.injEq]
      omega
    all_goals omega
  | msgRing opcode source payload =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.msgRing.injEq]
      omega
    all_goals omega
  | msgRingSent => decide
  | channel id =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.channel.injEq]
      omega
    all_goals omega
  | timer job =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.timer.injEq]
      omega
    all_goals omega

/-- **Injectivity across the whole space**: two well-formed tokens with the
same 64-bit encoding are the same token — no completion can be misrouted
between namespaces or between distinct objects of one namespace. -/
theorem encode_inj {a b : Token} (ha : a.Wf) (hb : b.Wf)
    (h : a.encode = b.encode) : a = b := by
  have hda := decode_encode a ha
  have hdb := decode_encode b hb
  rw [h] at hda
  exact Option.some.inj (hda.symm.trans hdb)

/-- The all-ones corner of the message-ring namespace is literally the cancel
sentinel. Well-formedness excludes exactly this point; a dispatch chain that
checks the cancel sentinel first resolves the alias silently at run time. -/
theorem msgRing_corner_aliases_cancel :
    encode (.msgRing 0xFF 0xFFFF (2 ^ 32 - 1)) = encode .cancel := by decide

/-- ... and that corner is not well-formed. -/
theorem msgRing_corner_not_wf : ¬ Wf (.msgRing 0xFF 0xFFFF (2 ^ 32 - 1)) := by
  decide

/-- **The generation bound is load-bearing.** With the `generation < 2^31`
bound dropped, a slab key collides with a multishot-recv tag: slot 5 at
reuse generation `0xBECF0000` encodes identically to the recv tag for
socket fd 5 — the completion for the pending op would dispatch as inbound
data for an unrelated socket. A free-running 32-bit generation counter
passes through windows like this one for every tagged namespace. -/
theorem slab_generation_overflow_collides :
    encode (.slab 5 0xBECF0000) = encode (.recvMulti 5) := by decide

/-- ... and that key is not well-formed. -/
theorem slab_generation_overflow_not_wf : ¬ Wf (.slab 5 0xBECF0000) := by
  decide

/-- Slot 0 is reserved: a zero slab key would collide with the wakeup
sentinel. (`Wf` requires `0 < index`.) -/
theorem slab_zero_aliases_wakeup :
    encode (.slab 0 0) = encode .wakeup := by decide

end Token

/-!
## The timeout-token sub-space

Kernel-timeout completions carry a *second* token — the timeout user token —
delivered through the timeout dispatch callback rather than the raw
completion word (the timeout operation itself rides a slab key). This
sub-space is partitioned by the top two bits:

  * bit 63 set — periodic-job tokens, job id in the low 63 bits;
  * bit 62 set, bit 63 clear — sweep-timer tokens, small id in the low bits,
    with one distinguished id (`20`) reserved for the connection deadline
    queue and matched exactly before the sweep test;
  * both clear — plain per-object tokens (below `2^62`).
-/

/-- The timeout-token namespaces. -/
inductive TimeoutToken where
  /-- A periodic job: bit 63 set, job id in the low 63 bits. -/
  | periodic (job : Nat)
  /-- The connection deadline queue's distinguished token: sweep id `20`. -/
  | deadlineMain
  /-- A sweep timer: bit 62 set, bit 63 clear, id in the low bits;
  id `20` is reserved for `deadlineMain`. -/
  | sweep (id : Nat)
  /-- A plain per-object token, below `2^62`. -/
  | plain (v : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace TimeoutToken

/-- Field bounds per namespace. -/
def Wf : TimeoutToken → Prop
  | .periodic job => job < 2 ^ 63
  | .deadlineMain => True
  | .sweep id => id < 2 ^ 62 ∧ id ≠ 20
  | .plain v => v < 2 ^ 62

instance (t : TimeoutToken) : Decidable t.Wf := by
  cases t <;> (simp only [Wf]; infer_instance)

/-- Encode a timeout token. -/
def encode : TimeoutToken → Nat
  | .periodic job => 2 ^ 63 + job
  | .deadlineMain => 2 ^ 62 + 20
  | .sweep id => 2 ^ 62 + id
  | .plain v => v

/-- Decode, in dispatch priority order: the distinguished deadline token is
matched exactly first, then bit 63 (periodic), then bit 62 (sweep). -/
def decode (v : Nat) : Option TimeoutToken :=
  if v = 2 ^ 62 + 20 then some .deadlineMain
  else if 2 ^ 63 ≤ v then some (.periodic (v - 2 ^ 63))
  else if 2 ^ 62 ≤ v then some (.sweep (v - 2 ^ 62))
  else some (.plain v)

/-- Round-trip on well-formed timeout tokens. -/
theorem decode_encode (t : TimeoutToken) (h : t.Wf) : decode t.encode = some t := by
  cases t with
  | periodic job =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_pos]
    · simp only [Option.some.injEq, TimeoutToken.periodic.injEq]
      omega
    all_goals omega
  | deadlineMain => decide
  | sweep id =>
    obtain ⟨h1, h2⟩ := h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, TimeoutToken.sweep.injEq]
      omega
    all_goals omega
  | plain v =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg]
    all_goals omega

/-- Injectivity of the timeout-token encoding on well-formed tokens. -/
theorem encode_inj {a b : TimeoutToken} (ha : a.Wf) (hb : b.Wf)
    (h : a.encode = b.encode) : a = b := by
  have hda := decode_encode a ha
  have hdb := decode_encode b hb
  rw [h] at hda
  exact Option.some.inj (hda.symm.trans hdb)

/-- Sweep id 20 is reserved: it encodes to the distinguished deadline
token. `Wf` excludes it from the sweep namespace. -/
theorem sweep_20_aliases_deadlineMain :
    encode (.sweep 20) = encode .deadlineMain := by decide

end TimeoutToken

end Flow
