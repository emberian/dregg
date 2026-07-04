/-
# The rotating XOR mask (RFC 6455 §5.3)

A masked frame carries a 4-byte masking key. The transformed octet `i` of the
payload is `original[i] XOR key[i mod 4]`; the same operation applied a second
time restores the original, since XOR with a fixed byte is an involution. The
receiver runs exactly this to unmask.

Headline results:

* `applyMask_involution` — masking then masking again with the same key is the
  identity, so unmasking is the inverse of masking (they are the same map).
* `applyMask_length` — masking preserves payload length (it is a per-octet map).

The masking direction rule (a client-to-server frame MUST be masked) is a
well-formedness predicate on the parsed frame; it lives in `Ws.Frame`.
-/
import Ws.Basic

namespace Ws

/-- XOR with a fixed byte is an involution: `(a ⊕ b) ⊕ b = a`. -/
theorem u8_xor_cancel (a b : UInt8) : (a ^^^ b) ^^^ b = a := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt8.toBitVec_xor]
  simp [BitVec.xor_assoc]

/-- Apply the rotating mask starting at payload index `i`: octet `j` (absolute)
is XORed with `key[j mod 4]`. A missing key byte defaults to `0` (the identity
for XOR), so a malformed short key degrades to leaving those octets untouched
rather than trapping. -/
def maskFrom (key : Bytes) : Nat → Bytes → Bytes
  | _, [] => []
  | i, b :: bs => (b ^^^ key.getD (i % 4) 0) :: maskFrom key (i + 1) bs

/-- Mask (or unmask) a payload with a 4-byte key, starting at index `0`. Masking
and unmasking are the same operation (see `applyMask_involution`). -/
def applyMask (key : Bytes) (p : Bytes) : Bytes := maskFrom key 0 p

/-- Masking preserves length — it is a per-octet map. -/
theorem maskFrom_length (key : Bytes) : ∀ (i : Nat) (p : Bytes),
    (maskFrom key i p).length = p.length
  | _, [] => rfl
  | i, b :: bs => by
    show (maskFrom key (i + 1) bs).length + 1 = bs.length + 1
    rw [maskFrom_length key (i + 1) bs]

/-- **Masking is an involution**: applying the mask twice with the same key from
the same offset restores the payload. Unmasking is therefore the inverse of
masking — the receiver recovers the original bytes exactly. -/
theorem maskFrom_involution (key : Bytes) : ∀ (i : Nat) (p : Bytes),
    maskFrom key i (maskFrom key i p) = p
  | _, [] => rfl
  | i, b :: bs => by
    show ((b ^^^ key.getD (i % 4) 0) ^^^ key.getD (i % 4) 0)
        :: maskFrom key (i + 1) (maskFrom key (i + 1) bs) = b :: bs
    rw [u8_xor_cancel, maskFrom_involution key (i + 1) bs]

/-- **Unmask ∘ mask = id**: `applyMask key` is its own inverse. Masking a
payload then unmasking with the same key yields the original payload. -/
theorem applyMask_involution (key : Bytes) (p : Bytes) :
    applyMask key (applyMask key p) = p :=
  maskFrom_involution key 0 p

/-- Masking preserves payload length. -/
theorem applyMask_length (key : Bytes) (p : Bytes) :
    (applyMask key p).length = p.length :=
  maskFrom_length key 0 p

end Ws
