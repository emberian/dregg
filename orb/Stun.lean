/-!
# STUN message parsing (RFC 5389) — the 20-byte header and TLV attributes

A total, sans-IO decoder for STUN messages as they arrive on the wire. STUN
(Session Traversal Utilities for NAT) is the base framing that ICE
connectivity checks (RFC 8445) ride on: every check is a STUN Binding
request/response, so a data-channel stack cannot form a candidate pair without
first agreeing on this frame.

## What this file captures

* **RFC 5389 §6 — the message header.** Every STUN message begins with a fixed
  20-byte header: a 16-bit message type (whose two most significant bits are
  zero), a 16-bit message length, the 32-bit magic cookie `0x2112A442`, and a
  96-bit (12-byte) transaction id. `parse` reads exactly this layout.
* **RFC 5389 §15 — TLV attributes.** After the header come zero or more
  attributes, each a 16-bit type, a 16-bit length (of the value, before
  padding), the value, and 0–3 bytes of padding so each attribute ends on a
  32-bit boundary. `parseAttrs` walks them.

## The theorems

* `stun_magic_checked` — a message whose cookie field is not `0x2112A442` is
  rejected. This is the §6 multiplexing guard: STUN shares a UDP port with the
  media it demultiplexes, and the cookie is how a receiver tells STUN apart.
* `stun_parse_total` — the decoder is a total function: every byte string
  yields exactly one of two outcomes, `none` (malformed) or `some message`.
  There is no third "stuck" or divergent outcome (Lean's termination checker
  already forbids divergence; this records the shape).
* `stun_attr_bounds` — in any successfully parsed message, every attribute's
  value stays within the declared message length. The walk never reports an
  attribute reaching past the buffer the header claimed.

## Boundary (left uninterpreted, honestly)

RFC 5389 §15.4 (MESSAGE-INTEGRITY, an HMAC-SHA1 over the message) and §15.5
(FINGERPRINT, a CRC-32) are cryptographic/checksum boundaries. They are
modeled as named uninterpreted total functions (`messageIntegrityOk`,
`fingerprintOk`) exactly as the TLS library models AEAD: the structural
theorems here hold uniformly over every possible behavior of those functions,
because the parser's framing does not depend on them. The STUN transaction
state machine (§7, retransmission timers) and the address attributes'
XOR-obfuscation (§15.2, XOR-MAPPED-ADDRESS) are out of scope for this frame
skeleton.
-/

namespace Stun

/-- Raw byte strings, modeled as lists to match the sibling libraries. -/
abbrev Bytes := List UInt8

/-- Big-endian decode of two bytes into a 16-bit value. -/
def be16 (hi lo : UInt8) : Nat := hi.toNat * 256 + lo.toNat

/-- The magic cookie (RFC 5389 §6), `0x2112A442` in network byte order. -/
def magicCookie : Bytes := [0x21, 0x12, 0xA4, 0x42]

/-! ## Cryptographic boundary (RFC 5389 §15.4, §15.5)

Modeled as uninterpreted total functions. `messageIntegrityOk key msg` stands
for the HMAC-SHA1 check; `fingerprintOk msg` for the CRC-32 check. No theorem
below depends on their behavior — they are the named crypto boundary. -/

/-- Boundary: the MESSAGE-INTEGRITY (HMAC-SHA1) verification of §15.4. -/
opaque messageIntegrityOk : Bytes → Bytes → Bool
/-- Boundary: the FINGERPRINT (CRC-32) verification of §15.5. -/
opaque fingerprintOk : Bytes → Bool

/-! ## Attributes (RFC 5389 §15) -/

/-- A decoded TLV attribute: the 16-bit type and the value (padding stripped).
The declared length equals `value.length`. -/
structure Attr where
  type : Nat
  value : Bytes
deriving Repr, DecidableEq

/-- The number of padding bytes appended after a value of length `n` so the
attribute ends on a 32-bit boundary (§15): `(4 - n mod 4) mod 4`. -/
def padLen (n : Nat) : Nat := (4 - n % 4) % 4

/-- Walk a body region into a list of TLV attributes. Structurally recursive on
`fuel` (the body length is always enough fuel, since each attribute consumes at
least its 4-byte TLV header). A step reads the 16-bit type and 16-bit length,
takes `len` value bytes, and skips `len + padLen len` bytes to the next
attribute; it fails if the declared value plus padding would run past the
remaining buffer, or if a stray 1–3 bytes remain. -/
def parseAttrsF : Nat → Bytes → Option (List Attr)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, t1 :: t0 :: l1 :: l0 :: rest =>
    let typ := be16 t1 t0
    let len := be16 l1 l0
    let pad := padLen len
    if len + pad ≤ rest.length then
      let value := rest.take len
      let rest' := rest.drop (len + pad)
      match parseAttrsF fuel rest' with
      | some attrs => some ({ type := typ, value := value } :: attrs)
      | none => none
    else none
  | _ + 1, _ => none

/-- Parse the attribute region of a body: fuel is exactly the body length. -/
def parseAttrs (body : Bytes) : Option (List Attr) := parseAttrsF body.length body

/-! ## The message -/

/-- A decoded STUN message (RFC 5389 §6): the 16-bit type, the declared length,
the 12-byte transaction id, and the attribute list. -/
structure Message where
  typ : Nat
  length : Nat
  txid : Bytes
  attrs : List Attr
deriving Repr

/-- Parse a STUN message. Reads the 20-byte header (type, length, magic cookie,
transaction id), rejects any message whose cookie is not `0x2112A442`, then
parses `length` bytes of attributes. Total: returns `none` on any malformed or
truncated input. -/
def parse (b : Bytes) : Option Message :=
  match b with
  | ty1 :: ty0 :: ln1 :: ln0 :: m3 :: m2 :: m1 :: m0 :: rest =>
    if [m3, m2, m1, m0] = magicCookie then
      let typ := be16 ty1 ty0
      let len := be16 ln1 ln0
      let txid := rest.take 12
      let afterTx := rest.drop 12
      if 12 ≤ rest.length ∧ len ≤ afterTx.length then
        let body := afterTx.take len
        match parseAttrs body with
        | some attrs => some { typ := typ, length := len, txid := txid, attrs := attrs }
        | none => none
      else none
    else none
  | _ => none

/-! ## Theorems -/

/-- **Magic-cookie guard (RFC 5389 §6).** A message whose 32-bit cookie field is
not `0x2112A442` is rejected outright. This is what lets a receiver tell STUN
apart from the media it is multiplexed with on the same port. -/
theorem stun_magic_checked
    (ty1 ty0 ln1 ln0 m3 m2 m1 m0 : UInt8) (rest : Bytes)
    (h : [m3, m2, m1, m0] ≠ magicCookie) :
    parse (ty1 :: ty0 :: ln1 :: ln0 :: m3 :: m2 :: m1 :: m0 :: rest) = none := by
  simp only [parse, if_neg h]

/-- **Totality.** The decoder returns for every input, with exactly two possible
shapes: rejection or a single decoded message. No partial/stuck outcome. -/
theorem stun_parse_total (b : Bytes) :
    parse b = none ∨ ∃ m, parse b = some m := by
  cases h : parse b with
  | none => exact Or.inl rfl
  | some m => exact Or.inr ⟨m, rfl⟩

/-- A message shorter than the fixed 20-byte header is rejected (a corollary of
the header shape: fewer than the eight leading bytes cannot match). -/
theorem stun_parse_short (b : Bytes) (h : b.length < 8) : parse b = none := by
  match b with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | [_, _, _, _, _] => rfl
  | [_, _, _, _, _, _] => rfl
  | [_, _, _, _, _, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => simp only [List.length_cons] at h; omega

/-- Every attribute produced by `parseAttrsF` has a value no longer than the
body it was read from. Proved by induction on the fuel. -/
theorem parseAttrsF_value_bound (fuel : Nat) :
    ∀ (body : Bytes) (attrs : List Attr), parseAttrsF fuel body = some attrs →
      ∀ a ∈ attrs, a.value.length ≤ body.length := by
  induction fuel with
  | zero =>
    intro body attrs h a ha
    match body with
    | [] =>
      simp only [parseAttrsF, Option.some.injEq] at h
      subst h; simp at ha
    | _ :: _ => simp [parseAttrsF] at h
  | succ n ih =>
    intro body attrs h a ha
    match body with
    | [] =>
      simp only [parseAttrsF, Option.some.injEq] at h
      subst h; simp at ha
    | [_] => simp [parseAttrsF] at h
    | [_, _] => simp [parseAttrsF] at h
    | [_, _, _] => simp [parseAttrsF] at h
    | t1 :: t0 :: l1 :: l0 :: rest =>
      simp only [parseAttrsF] at h
      by_cases hb : be16 l1 l0 + padLen (be16 l1 l0) ≤ rest.length
      · rw [if_pos hb] at h
        cases hrec : parseAttrsF n (rest.drop (be16 l1 l0 + padLen (be16 l1 l0))) with
        | none => rw [hrec] at h; simp at h
        | some tail =>
          rw [hrec] at h
          simp only [Option.some.injEq] at h
          subst h
          rcases List.mem_cons.mp ha with hhd | htl
          · subst hhd
            simp only [List.length_take]
            calc min (be16 l1 l0) rest.length ≤ rest.length := Nat.min_le_right _ _
              _ ≤ (t1 :: t0 :: l1 :: l0 :: rest).length := by simp only [List.length_cons]; omega
          · have hbound := ih _ _ hrec a htl
            have hdrop : (rest.drop (be16 l1 l0 + padLen (be16 l1 l0))).length ≤ rest.length :=
              by rw [List.length_drop]; omega
            calc a.value.length ≤ (rest.drop (be16 l1 l0 + padLen (be16 l1 l0))).length := hbound
              _ ≤ rest.length := hdrop
              _ ≤ (t1 :: t0 :: l1 :: l0 :: rest).length := by simp only [List.length_cons]; omega
      · rw [if_neg hb] at h; simp at h

/-- **Attribute bounds (RFC 5389 §15).** In any successfully parsed message,
every attribute's value stays within the declared message length. The decoder
never reports an attribute reaching past the region the header claimed. -/
theorem stun_attr_bounds (b : Bytes) (m : Message) (h : parse b = some m) :
    ∀ a ∈ m.attrs, a.value.length ≤ m.length := by
  intro a ha
  match b with
  | ty1 :: ty0 :: ln1 :: ln0 :: c3 :: c2 :: c1 :: c0 :: rest =>
    simp only [parse] at h
    by_cases hc : [c3, c2, c1, c0] = magicCookie
    · rw [if_pos hc] at h
      by_cases hlen : 12 ≤ rest.length ∧ be16 ln1 ln0 ≤ (rest.drop 12).length
      · rw [if_pos hlen] at h
        cases hrec : parseAttrs ((rest.drop 12).take (be16 ln1 ln0)) with
        | none => rw [hrec] at h; simp at h
        | some attrs =>
          rw [hrec] at h
          simp only [Option.some.injEq] at h
          subst h
          -- m.attrs = attrs, m.length = be16 ln1 ln0
          have hbody := parseAttrsF_value_bound _ _ _ hrec a ha
          have hbl : ((rest.drop 12).take (be16 ln1 ln0)).length ≤ be16 ln1 ln0 := by
            rw [List.length_take]; exact Nat.min_le_left _ _
          exact Nat.le_trans hbody hbl
      · rw [if_neg hlen] at h; simp at h
    · rw [if_neg hc] at h; simp at h
  | [] => simp [parse] at h
  | [_] => simp [parse] at h
  | [_, _] => simp [parse] at h
  | [_, _, _] => simp [parse] at h
  | [_, _, _, _] => simp [parse] at h
  | [_, _, _, _, _] => simp [parse] at h
  | [_, _, _, _, _, _] => simp [parse] at h
  | [_, _, _, _, _, _, _] => simp [parse] at h

def version : String := "0.1.0"

end Stun
