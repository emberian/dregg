/-
# Dregg2.Circuit.KeyLanes9 — THE OWNER-KEY OCTET. A CANONICITY WRAP CANNOT CLOSE IT.

## SUBSTRATE, SAID OUT LOUD

This is Lean-authored AIR material. Nothing here is written in Rust; the companion
`Dregg2.Circuit.Emit.KeyCanonicity9Emit` emits the constraints and Rust only re-reads them.

## The brief this file REFUTES, and the one it answers instead

`Dregg2.Circuit.Emit.FieldsCanonicity9Emit` closed the FIELDS octet on 2026-07-31 by emitting
`FieldLanes9.Canonical9` — an envelope forcing the committed columns into the encoder's image. The
obvious next move is "apply the same treatment to the owner-key octet at `B_PUBKEY_OCTET`".

**It does not transfer, and the reason is structural.** The fields wrap was a canonicity envelope
around an ALREADY-INJECTIVE nine-lane encoder: `fieldToLanes9_injective` was a theorem, and the only
thing missing was that a prover picks COLUMNS rather than VALUES. The owner-key octet is broken on
BOTH axes at once:

  * **the columns are unforced** — measured 2026-07-31 across all 117 rotated members of both
    emitted registries, the sixteen columns `before_base + {0, B_SPAN} + 105 .. +112` carry ZERO
    range lookups, ZERO `colEq` welds, ZERO gate-body appearances and ZERO `pi_binding`s. Strictly
    emptier than the fields octet was (fields lane 0 was at least welded to the v1 face);
  * **and the ENCODER IS NOT INJECTIVE.** `dregg_commit::typed::canonical_32_to_felts_8` (byte-twins
    at `dregg_cell::commitment::canonical_to_babybear_pi`, `dregg_storage::commitment`, and inlined
    in `circuit/src/effect_vm/trace.rs`) packs `lo | mid1<<8 | mid2<<16 | (hi & 0x3F)<<24` — `8+8+8+6
    = 30` bits per limb. **Bits 6-7 of bytes 3, 7, 11, 15, 19, 23, 27, 31 are DISCARDED**: 16 source
    bits, unbound.

A canonicity envelope forces the columns into the image of a map that is not injective on its
domain. §2's `eight_lane_canonicity_is_not_a_repair` is that sentence as a machine-checked exhibit:
two DISTINCT 32-byte keys whose octets are equal AND fully canonical. **The wrap, fully forced,
still admits a second preimage — constructed, not searched, one bit flip.** Emitting the eight-lane
wrap alone would be shipping a containment while naming the real fix as a later phase.

## What this file authors instead: the ninth lane, and its canonicity

§3 is the replacement encoder — a base-`2^29` NONET over the 32 bytes, little-endian:

```text
  keyWord b = ofDigits 256 [b 0, …, b 31]              -- the key as a 256-bit number
  keyToLanes9 b i = the i-th base-2^29 digit of it     -- nine lanes, i = 0..8
```

`2^29 = 536870912 < p`, so **no lane ever reduces**; `8·29 = 232 < 256 ≤ 9·29 = 261`, so nine is the
minimum and eight is refuted by `FieldLanes9.nine_lanes_is_the_minimum` (`P^8 < 2^256`) — the same
pigeonhole `MapOpWideKeyPigeonhole.no_injection_bytes32_to_canonKey8` already carries for the
arity-17 address slot. `keyLanes9ToBytes` is a TOTAL decoder and `keyToLanes9_injective` follows
from a machine-checked left inverse. Not a hash bound.

§4 is the canonicity envelope, and it has exactly **two legs and no gates**:

  1. `LanesRanged` — lanes 0..7 below `2^29`. *Eight range lookups.*
  2. `TopLaneRanged` — lane 8 below `2^24`. *ONE range lookup, at a DIFFERENT width.*

`canonicalKey9_iff_in_image` proves the two together are EXACTLY the image. No `NoWrap` leg, no cube
gate, no aux columns: the fields octet needed those because its lanes 0/1 were a `mod p` REDUCTION
it could not move (welded to the v1 face). The key octet is welded to nothing, so the encoding was
replaced wholesale and the reduction disappeared with it.

⚑ **AND LEG 2 IS NOT A CONSEQUENCE OF LEG 1 — that is the exhibit.** `forgedKeyNonet = [0,…,0,2^24]`
has every lane below `2^29`, so it passes a UNIFORM nine-lane `< 2^29` lookup — the naive reading of
"range-check the lanes". Its value is `2^24 · (2^29)^8 = 2^256`, which the total decoder reads
modulo `2^256` as the ALL-ZERO key. So it decodes byte-for-byte to the honest zero key's decode
while being a different committed vector. `uniform_lane_ranges_do_not_force_the_image` is that, and
it is the exact structural twin of `FieldLanes9.free_lane_ranges_alone_do_not_force_the_image`.

## ⚑ THE PRICE, SAID OUT LOUD — this is a RE-GENESIS, not a re-emit

The fields wrap was cheap because its 112 aux columns rode the appendix, past every committed limb.
**A ninth KEY lane cannot ride the appendix**: an appendix column is not in `preLimbsAt`, so it
never enters the `wireCommitR` absorption chain, so it is a free felt carrying nothing — `state_commit`
would still bind only 232 bits of the key. The ninth lane must be an ABSORBED PRE-LIMB.

  * the pre-limb region was **184/184 full** (`ROTATED_PADS` is `[usize; 0]`; the two former pads were
    eaten by the fields nonet), so `rotatedNumPreLimbs` had to GROW;
  * ⚑ and it had to grow to **187, not 185**. `B_SPAN := n + 3 + (n − 4) / 3` is `Nat` floor division
    while the real carrier chain is `chunk31`, whose `chunkCount (n+3) = chunkCount n + 1`. At
    `n = 185` the formula gives 60 and the chain needs 61 — the block is silently under-allocated by
    one carrier column. The invariant nobody wrote down is `rotatedNumPreLimbs ≡ 1 (mod 3)`.
    `184 → 187` buys exactly three limbs: one ninth lane each for `public_key`, `child_vk` and
    `contract_hash`, all three of which are 8-lane and all three of which this counting kills.
  * growing the pre-limbs moves every `state_commit`, so `persist`'s
    `CANONICAL_STATE_SCHEMA_EPOCH` must be bumped and the chain re-genesised. (Do not transcribe a
    remembered epoch number: read the constant.)

✅ **LANDED 2026-08-01 — `rotatedNumPreLimbs` IS 187.** `RotatedLayout.rotated196` allocates the
three ninth lanes at in-block limbs 184 (`child_vk`), 185 (`contract_hash`) and 186
(**`public_key`**), `Legal.octetNonets` makes an octet without a ninth lane unconstructable, and
`EffectVmEmitRotationV3.preLimbsAt` now folds all 187 — so the owner key's ninth lane is inside the
list `wireCommitR` absorbs. The companion's `deployedKeyCanon9Cols` has NO free column left but the
face width, `deployed_nonet_is_absorbed` proves all nine lanes are absorbed pre-limbs, and
`keyCanon9_determines_the_owner_key_deployed` states the capstone against `preLimbsAt` entries
rather than bare columns.

⚠ **WHAT THIS FILE STILL DOES NOT REACH.** The envelope is authored, proved and geometrically
placed; it is NOT yet appended to any live member's constraint list, no descriptor has been
re-emitted, no VK rotated and no chain re-genesised. A Rust `key_limbs9` producer must fill limb 186
(and 184/185) or every honest turn is UNSAT. State that rung exactly and do not round it up.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`.
-/
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Dregg2.Circuit.FieldLanes9
import Dregg2.Tactics

namespace Dregg2.Circuit.KeyLanes9

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 20000

open Dregg2.Circuit.FieldLanes9 (P Byte Bytes32 ofDigits digitsN ofDigits_append ofDigits_lt
  ofDigits_digitsN digitsN_ofDigits digitsN_lt digitsN_length nine_lanes_is_the_minimum)

/-! ## §0 — one positional lemma the fields file did not export at this shape.

⚠ `Dregg2.Circuit.Emit.FieldsCanonicity9Emit.digitsN_getD` is the same statement. It is re-proved
here rather than imported because THIS is a model file and that is an emit file: importing the emit
chain (`EffectVmEmitRotationV3`, ~6k lines) into a counting module to borrow ten lines would invert
the dependency. When one of the two moves into `FieldLanes9` proper, delete the other. -/

/-- Digit `j` of a `k`-digit base-`b` expansion is `n / b^j % b`. -/
theorem digitsN_getD (b : Nat) (hb : 0 < b) :
    ∀ (k j n : Nat), j < k → (digitsN b k n).getD j 0 = n / b ^ j % b := by
  intro k
  induction k with
  | zero => intro j n hj; omega
  | succ k ih =>
    intro j n hj
    cases j with
    | zero => simp [digitsN]
    | succ j =>
      have hjk : j < k := by omega
      simp only [digitsN, List.getD_cons_succ, ih j (n / b) hjk]
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm (b ^ j) b]

/-- Eta for a 32-element list read through `getD`. Used to recompose the decoder's byte view. -/
private theorem list32_eta (l : List Nat) (h : l.length = 32) :
    [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0,
     l.getD 7 0, l.getD 8 0, l.getD 9 0, l.getD 10 0, l.getD 11 0, l.getD 12 0, l.getD 13 0,
     l.getD 14 0, l.getD 15 0, l.getD 16 0, l.getD 17 0, l.getD 18 0, l.getD 19 0, l.getD 20 0,
     l.getD 21 0, l.getD 22 0, l.getD 23 0, l.getD 24 0, l.getD 25 0, l.getD 26 0, l.getD 27 0,
     l.getD 28 0, l.getD 29 0, l.getD 30 0, l.getD 31 0] = l := by
  rcases l with _ | ⟨a0, l⟩; · simp at h
  rcases l with _ | ⟨a1, l⟩; · simp at h
  rcases l with _ | ⟨a2, l⟩; · simp at h
  rcases l with _ | ⟨a3, l⟩; · simp at h
  rcases l with _ | ⟨a4, l⟩; · simp at h
  rcases l with _ | ⟨a5, l⟩; · simp at h
  rcases l with _ | ⟨a6, l⟩; · simp at h
  rcases l with _ | ⟨a7, l⟩; · simp at h
  rcases l with _ | ⟨a8, l⟩; · simp at h
  rcases l with _ | ⟨a9, l⟩; · simp at h
  rcases l with _ | ⟨a10, l⟩; · simp at h
  rcases l with _ | ⟨a11, l⟩; · simp at h
  rcases l with _ | ⟨a12, l⟩; · simp at h
  rcases l with _ | ⟨a13, l⟩; · simp at h
  rcases l with _ | ⟨a14, l⟩; · simp at h
  rcases l with _ | ⟨a15, l⟩; · simp at h
  rcases l with _ | ⟨a16, l⟩; · simp at h
  rcases l with _ | ⟨a17, l⟩; · simp at h
  rcases l with _ | ⟨a18, l⟩; · simp at h
  rcases l with _ | ⟨a19, l⟩; · simp at h
  rcases l with _ | ⟨a20, l⟩; · simp at h
  rcases l with _ | ⟨a21, l⟩; · simp at h
  rcases l with _ | ⟨a22, l⟩; · simp at h
  rcases l with _ | ⟨a23, l⟩; · simp at h
  rcases l with _ | ⟨a24, l⟩; · simp at h
  rcases l with _ | ⟨a25, l⟩; · simp at h
  rcases l with _ | ⟨a26, l⟩; · simp at h
  rcases l with _ | ⟨a27, l⟩; · simp at h
  rcases l with _ | ⟨a28, l⟩; · simp at h
  rcases l with _ | ⟨a29, l⟩; · simp at h
  rcases l with _ | ⟨a30, l⟩; · simp at h
  rcases l with _ | ⟨a31, l⟩; · simp at h
  rcases l with _ | ⟨a32, l⟩
  · rfl
  · simp at h

private theorem list9_eta (l : List Nat) (h : l.length = 9) :
    [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0,
     l.getD 7 0, l.getD 8 0] = l := by
  rcases l with _ | ⟨a0, l⟩; · simp at h
  rcases l with _ | ⟨a1, l⟩; · simp at h
  rcases l with _ | ⟨a2, l⟩; · simp at h
  rcases l with _ | ⟨a3, l⟩; · simp at h
  rcases l with _ | ⟨a4, l⟩; · simp at h
  rcases l with _ | ⟨a5, l⟩; · simp at h
  rcases l with _ | ⟨a6, l⟩; · simp at h
  rcases l with _ | ⟨a7, l⟩; · simp at h
  rcases l with _ | ⟨a8, l⟩; · simp at h
  rcases l with _ | ⟨a9, l⟩
  · rfl
  · simp at h

/-! ## §1 — THE DEPLOYED EIGHT-LANE KEY PACKER, as a Lean twin.

`canonical_32_to_felts_8(canonical)[i] = lo | mid1<<8 | mid2<<16 | ((hi & 0x3F) << 24)` over
`canonical[4i .. 4i+4]`. Byte-for-byte the deployed shape, including the `& 0x3F`. -/

/-- The deployed owner-key carrier: eight BabyBear limbs at `B_PUBKEY_OCTET .. +8`. -/
abbrev Octet := Fin 8 → Nat

/-- `2^30` — the packer's per-limb ceiling. Note `2^30 < p`, so the limb never reduces; the loss is
NOT a modular one, it is the `& 0x3F`. -/
def LIMB30 : Nat := 1073741824

theorem LIMB30_lt_P : LIMB30 < P := by decide

/-- Limb `i` of the deployed packer. The `% 64` IS the `& 0x3F` — two source bits dropped per limb,
sixteen over the octet. -/
def keyLimb (b : Bytes32) (i : Fin 8) : Nat :=
  (b ⟨4 * i.1, by have := i.isLt; omega⟩).1
    + 256 * (b ⟨4 * i.1 + 1, by have := i.isLt; omega⟩).1
    + 65536 * (b ⟨4 * i.1 + 2, by have := i.isLt; omega⟩).1
    + 16777216 * ((b ⟨4 * i.1 + 3, by have := i.isLt; omega⟩).1 % 64)

/-- **THE DEPLOYED ENCODER.** -/
def keyToLanes8 (b : Bytes32) : Octet := keyLimb b

/-- Every deployed limb is below `2^30` — so the deployed canonicity envelope, if it were emitted,
would be eight `< 2^30` range lookups per block and nothing else. -/
theorem keyToLanes8_lt (b : Bytes32) (i : Fin 8) : keyToLanes8 b i < LIMB30 := by
  have h0 := (b ⟨4 * i.1, by have := i.isLt; omega⟩).2
  have h1 := (b ⟨4 * i.1 + 1, by have := i.isLt; omega⟩).2
  have h2 := (b ⟨4 * i.1 + 2, by have := i.isLt; omega⟩).2
  have h3 : (b ⟨4 * i.1 + 3, by have := i.isLt; omega⟩).1 % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [keyToLanes8, keyLimb, LIMB30]
  omega

/-- The canonicity envelope an eight-lane wrap would force: every limb a genuine 30-bit digit. -/
def KeyCanonical8 (L : Octet) : Prop := ∀ i : Fin 8, L i < LIMB30

instance (L : Octet) : Decidable (KeyCanonical8 L) := by unfold KeyCanonical8; infer_instance

/-- COMPLETENESS POLE for the eight-lane wrap: it refuses no honest witness. -/
theorem keyCanonical8_of_encode (b : Bytes32) : KeyCanonical8 (keyToLanes8 b) :=
  fun i => keyToLanes8_lt b i

/-! ### The eight-lane image is EXACTLY `[0, 2^30)^8` — the wrap's best possible case.

Unlike the fields nonet there is no third leg to find: the packer is surjective onto the canonical
box, so `KeyCanonical8` is precisely the image and an eight-lane wrap can force nothing more. That
is what makes §2 a refutation rather than a hunt for a missing condition. -/

/-- A preimage for any canonical octet: byte `j` is base-256 digit `j % 4` of limb `j / 4`. -/
def key8Preimage (L : Octet) : Bytes32 := fun j =>
  ⟨(L ⟨j.1 / 4, by have := j.isLt; omega⟩) / 256 ^ (j.1 % 4) % 256, Nat.mod_lt _ (by decide)⟩

theorem keyToLanes8_key8Preimage {L : Octet} (h : KeyCanonical8 L) :
    keyToLanes8 (key8Preimage L) = L := by
  funext i
  have hi := h i
  simp only [LIMB30] at hi
  simp only [keyToLanes8, keyLimb, key8Preimage]
  fin_cases i <;> simp_all <;> omega

/-- **THE EIGHT-LANE IMAGE.** `KeyCanonical8` is exactly the deployed packer's image, so an emitted
eight-lane canonicity envelope is the strongest wrap of that shape that exists. -/
theorem keyCanonical8_iff_in_image (L : Octet) :
    KeyCanonical8 L ↔ ∃ b : Bytes32, keyToLanes8 b = L := by
  constructor
  · intro h; exact ⟨key8Preimage L, keyToLanes8_key8Preimage h⟩
  · rintro ⟨b, rfl⟩; exact keyCanonical8_of_encode b

/-! ## §2 — ⚑ THE REFUTATION: the canonicity wrap, FULLY FORCED, still admits a second preimage.

`zeroKey` and `bit6Key` differ in byte 3 — the key `0x00…00` against the key with `0x40` at index 3.
Both are 32-byte strings; they are DISTINCT. The packer's `& 0x3F` erases bit 6 of that byte, so
their octets are IDENTICAL and both are fully canonical. No search, no birthday bound, no hash
assumption: one bit flip, `O(1)`.

⚑ Byte 3 is not special. The same flip works at bytes 7, 11, 15, 19, 23, 27, 31, at bit 6 or bit 7 —
`2^16` strings share every octet. -/

/-- The all-zero 32-byte key. -/
def zeroKey : Bytes32 := fun _ => 0

/-- The same key with bit 6 of byte 3 set — the bit the packer's `& 0x3F` discards. -/
def bit6Key : Bytes32 := fun j => if j.1 = 3 then ⟨64, by decide⟩ else ⟨0, by decide⟩

/-- **THE EXHIBIT.** Two DISTINCT 32-byte keys, both encoding to the SAME octet, and that octet
fully `KeyCanonical8`. So an emitted eight-lane canonicity envelope — even the exact-image one of
`keyCanonical8_iff_in_image` — admits the forgery, and the committed octet does not determine the
owner key. This is why the fields treatment does not transfer. -/
theorem eight_lane_canonicity_is_not_a_repair :
    zeroKey ≠ bit6Key
    ∧ keyToLanes8 zeroKey = keyToLanes8 bit6Key
    ∧ KeyCanonical8 (keyToLanes8 zeroKey)
    ∧ KeyCanonical8 (keyToLanes8 bit6Key) := by
  refine ⟨?_, ?_, keyCanonical8_of_encode _, keyCanonical8_of_encode _⟩
  · intro h
    have : (zeroKey 3).1 = (bit6Key 3).1 := by rw [h]
    simp [zeroKey, bit6Key] at this
  · funext i; fin_cases i <;> simp [keyToLanes8, keyLimb, zeroKey, bit6Key]

/-- The deployed packer is NOT injective — stated as the negation, so it cannot be read as a caveat.
`keyToLanes8_not_injective` and `FieldLanes9.nine_lanes_is_the_minimum` are two independent reasons:
the first is a constructed collision in the deployed code, the second says no eight-lane scheme
whatsoever could have worked. -/
theorem keyToLanes8_not_injective : ¬ Function.Injective keyToLanes8 := by
  intro h
  exact eight_lane_canonicity_is_not_a_repair.1
    (h eight_lane_canonicity_is_not_a_repair.2.1)

/-- The counting half, restated at this site: eight BabyBear lanes carry `P^8 < 2^256`, so the
non-injectivity above is not an artifact of the `& 0x3F` — it is forced. -/
theorem eight_lanes_cannot_carry_a_key : P ^ 8 < 2 ^ 256 := nine_lanes_is_the_minimum.1

/-! ## §3 — THE REPLACEMENT: a base-`2^29` NONET, injective, with a total decoder.

Nothing reads an individual key lane anywhere in the tree — `keyCommitSpec` / `pubkeyCompress1Spec`
absorb the whole octet and `compress_member` recomputes from bytes — and the octet is welded to
nothing (measured: zero `colEq`, zero gates, zero PIs). So unlike the fields lanes 0/1 the encoding
can be replaced WHOLESALE, and the replacement is the simplest injective one that fits: the key read
as a 256-bit little-endian number, in base `2^29`. -/

/-- The ninth-lane radix, `2^29`. Strictly below `P`, so NO lane ever reduces. -/
def K : Nat := 536870912

/-- The top lane's ceiling, `2^24 = 2^256 / (2^29)^8`. ⚑ A DIFFERENT WIDTH from the other eight —
that difference is leg 2, and `uniform_lane_ranges_do_not_force_the_image` is why it is load-bearing. -/
def KTOP : Nat := 16777216

theorem K_lt_P : K < P := by decide
theorem KTOP_lt_K : KTOP < K := by decide

/-- The nine committed lanes. -/
abbrev Nonet := Fin 9 → Nat

/-- `(2^29)^8 · 2^24 = 2^256` — the fit is EXACT: nine lanes at this split carry a 32-byte key with
no slack, and `2^256 ≤ P^9` says nine BabyBear felts can hold it. -/
theorem K8_KTOP : K ^ 8 * KTOP = 2 ^ 256 := by norm_num [K, KTOP]

/-- The 32 key bytes, LOW INDEX FIRST (little-endian, the `raw_to_u16_le` convention). Written out
so the round-trip discharge reduces instead of unfolding an `ofFn`. -/
def keyBytes (b : Bytes32) : List Nat :=
  [(b ⟨0, by omega⟩).1, (b ⟨1, by omega⟩).1, (b ⟨2, by omega⟩).1, (b ⟨3, by omega⟩).1,
   (b ⟨4, by omega⟩).1, (b ⟨5, by omega⟩).1, (b ⟨6, by omega⟩).1, (b ⟨7, by omega⟩).1,
   (b ⟨8, by omega⟩).1, (b ⟨9, by omega⟩).1, (b ⟨10, by omega⟩).1, (b ⟨11, by omega⟩).1,
   (b ⟨12, by omega⟩).1, (b ⟨13, by omega⟩).1, (b ⟨14, by omega⟩).1, (b ⟨15, by omega⟩).1,
   (b ⟨16, by omega⟩).1, (b ⟨17, by omega⟩).1, (b ⟨18, by omega⟩).1, (b ⟨19, by omega⟩).1,
   (b ⟨20, by omega⟩).1, (b ⟨21, by omega⟩).1, (b ⟨22, by omega⟩).1, (b ⟨23, by omega⟩).1,
   (b ⟨24, by omega⟩).1, (b ⟨25, by omega⟩).1, (b ⟨26, by omega⟩).1, (b ⟨27, by omega⟩).1,
   (b ⟨28, by omega⟩).1, (b ⟨29, by omega⟩).1, (b ⟨30, by omega⟩).1, (b ⟨31, by omega⟩).1]

theorem keyBytes_length (b : Bytes32) : (keyBytes b).length = 32 := by simp [keyBytes]

theorem keyBytes_lt (b : Bytes32) : ∀ x ∈ keyBytes b, x < 256 := by
  intro x hx
  simp only [keyBytes, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst h <;> exact (b _).2

/-- The key as one 256-bit number. -/
def keyWord (b : Bytes32) : Nat := ofDigits 256 (keyBytes b)

theorem keyWord_lt (b : Bytes32) : keyWord b < 2 ^ 256 := by
  have h := ofDigits_lt 256 (by norm_num) (keyBytes b) (keyBytes_lt b)
  rw [keyBytes_length] at h
  calc keyWord b < 256 ^ 32 := h
    _ = 2 ^ 256 := by norm_num

/-- **THE ENCODER.** Nine base-`2^29` digits of the key. -/
def keyToLanes9 (b : Bytes32) : Nonet := fun i => (digitsN K 9 (keyWord b)).getD i.1 0

theorem keyToLanes9_lt_K (b : Bytes32) (i : Fin 9) : keyToLanes9 b i < K := by
  simp only [keyToLanes9]
  rcases Nat.lt_or_ge i.1 (digitsN K 9 (keyWord b)).length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact digitsN_lt K (by decide) 9 (keyWord b) _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]; decide

theorem keyToLanes9_lt_P (b : Bytes32) (i : Fin 9) : keyToLanes9 b i < P :=
  lt_trans (keyToLanes9_lt_K b i) K_lt_P

/-! ### THE DECODER — total, explicit, and the inverse. -/

def keyLaneList (L : Nonet) : List Nat := [L 0, L 1, L 2, L 3, L 4, L 5, L 6, L 7, L 8]

theorem keyLaneList_length (L : Nonet) : (keyLaneList L).length = 9 := by simp [keyLaneList]

/-- The 256-bit number the nine lanes recompose to. -/
def keyDecWord (L : Nonet) : Nat := ofDigits K (keyLaneList L)

/-- **THE DECODER.** Total on every lane vector; the exact inverse on the encoder's image. The
`% 256` is the truncation an off-image vector rides — `forgedKeyNonet` is exactly that. -/
def keyLanes9ToBytes (L : Nonet) : Bytes32 := fun j =>
  ⟨(digitsN 256 32 (keyDecWord L)).getD j.1 0 % 256, Nat.mod_lt _ (by decide)⟩

theorem keyDecWord_encode (b : Bytes32) : keyDecWord (keyToLanes9 b) = keyWord b := by
  have hshape : keyLaneList (keyToLanes9 b) = digitsN K 9 (keyWord b) := by
    simp only [keyLaneList, keyToLanes9]
    exact list9_eta _ (digitsN_length _ _ _)
  simp only [keyDecWord, hshape]
  refine ofDigits_digitsN K (by decide) 9 (keyWord b) ?_
  have h := keyWord_lt b
  have hk : (2 : Nat) ^ 256 ≤ K ^ 9 := by norm_num [K]
  omega

theorem digitsN_keyWord (b : Bytes32) : digitsN 256 32 (keyWord b) = keyBytes b := by
  have h := digitsN_ofDigits 256 (by norm_num) (keyBytes b) (keyBytes_lt b)
  rw [keyBytes_length] at h
  simpa [keyWord] using h

/-- **THE LEFT INVERSE.** Every 32-byte key round-trips through the nine lanes. -/
theorem keyLanes9ToBytes_keyToLanes9 (b : Bytes32) :
    keyLanes9ToBytes (keyToLanes9 b) = b := by
  funext j
  apply Fin.ext
  simp only [keyLanes9ToBytes, keyDecWord_encode, digitsN_keyWord]
  fin_cases j <;>
    simp only [keyBytes, List.getD_cons_zero, List.getD_cons_succ] <;>
    exact Nat.mod_eq_of_lt (b _).2

/-- **THE THEOREM.** The nine-lane key encoder is INJECTIVE: no two distinct 32-byte keys share a
lane vector. Not a hash bound, not a birthday bound — an injection with a machine-checked inverse.
Contrast `keyToLanes8_not_injective`, which is the deployed encoder. -/
theorem keyToLanes9_injective : Function.Injective keyToLanes9 := by
  intro a b h
  have := congrArg keyLanes9ToBytes h
  simpa [keyLanes9ToBytes_keyToLanes9] using this

#assert_axioms keyLanes9ToBytes_keyToLanes9
#assert_axioms keyToLanes9_injective
#assert_axioms eight_lane_canonicity_is_not_a_repair
#assert_axioms keyToLanes8_not_injective
#assert_axioms keyCanonical8_iff_in_image

/-! ## §4 — CANONICITY: the two legs, exactly the image, and the exhibit. -/

/-- Leg 1: lanes 0..7 are genuine base-`2^29` digits. **Eight range lookups at width 29.** -/
def LanesRanged (L : Nonet) : Prop := ∀ i : Fin 9, i.1 < 8 → L i < K

/-- **Leg 2 — THE ONE A UNIFORM LOOKUP DOES NOT GIVE.** The top lane's weight is `(2^29)^8 = 2^232`,
so it may carry only the remaining `2^24`. A lane-width (`< 2^29`) lookup on lane 8 leaves `2^5`
excess multiples of `2^256` available, and the total decoder reads the value modulo `2^256`.
**ONE range lookup, at width 24.** -/
def TopLaneRanged (L : Nonet) : Prop := L 8 < KTOP

/-- **THE AIR OBLIGATION.** Two legs, nine lookups per block, zero gates, zero aux columns. -/
def CanonicalKey9 (L : Nonet) : Prop := LanesRanged L ∧ TopLaneRanged L

/-- The naive reading of "range-check the nine lanes": ONE width for all of them. -/
def UniformRanged (L : Nonet) : Prop := ∀ i : Fin 9, L i < K

instance (L : Nonet) : Decidable (LanesRanged L) := by unfold LanesRanged; infer_instance
instance (L : Nonet) : Decidable (TopLaneRanged L) := by unfold TopLaneRanged; infer_instance
instance (L : Nonet) : Decidable (CanonicalKey9 L) := by unfold CanonicalKey9; infer_instance
instance (L : Nonet) : Decidable (UniformRanged L) := by unfold UniformRanged; infer_instance

theorem canonicalKey9_uniformRanged {L : Nonet} (h : CanonicalKey9 L) : UniformRanged L := by
  intro i
  rcases Nat.lt_or_ge i.1 8 with hi | hi
  · exact h.1 i hi
  · have : i = 8 := by apply Fin.ext; have := i.isLt; omega
    subst this
    exact lt_trans h.2 KTOP_lt_K

theorem keyLaneList_lt_of_uniform {L : Nonet} (h : UniformRanged L) :
    ∀ x ∈ keyLaneList L, x < K := by
  intro x hx
  simp only [keyLaneList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h'|h'|h'|h'|h'|h'|h'|h'|h' <;> subst h' <;> exact h _

/-- **THE BRIDGE.** Under leg 1 the two-leg envelope is EXACTLY the statement that the decoder's
recomposed value is a 32-byte key: `L 8 < 2^24 ↔ keyDecWord L < 2^256`. Both directions, so the
emitted width-24 lookup is a statement ABOUT THE DECODER and not a coincidentally similar number.
This is the `decCarry_eq_lane8_top` analogue, and it is an iff where that one was an equation. -/
theorem topLane_iff_decWord_lt {L : Nonet} (h : LanesRanged L) :
    TopLaneRanged L ↔ keyDecWord L < 2 ^ 256 := by
  have hsplit : keyDecWord L
      = ofDigits K [L 0, L 1, L 2, L 3, L 4, L 5, L 6, L 7] + K ^ 8 * L 8 := by
    have := ofDigits_append K [L 0, L 1, L 2, L 3, L 4, L 5, L 6, L 7] [L 8]
    simpa [keyDecWord, keyLaneList, ofDigits] using this
  have hlow : ofDigits K [L 0, L 1, L 2, L 3, L 4, L 5, L 6, L 7] < K ^ 8 := by
    have := ofDigits_lt K (by decide) [L 0, L 1, L 2, L 3, L 4, L 5, L 6, L 7] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact h _ (by decide))
    simpa using this
  rw [hsplit, ← K8_KTOP]
  simp only [TopLaneRanged]
  constructor
  · intro ht
    calc ofDigits K [L 0, L 1, L 2, L 3, L 4, L 5, L 6, L 7] + K ^ 8 * L 8
        < K ^ 8 + K ^ 8 * L 8 := Nat.add_lt_add_right hlow _
      _ = K ^ 8 * (L 8 + 1) := by ring
      _ ≤ K ^ 8 * KTOP := Nat.mul_le_mul_left _ ht
  · intro hw
    by_contra hc
    simp only [not_lt] at hc
    have hmul : K ^ 8 * KTOP ≤ K ^ 8 * L 8 := Nat.mul_le_mul_left _ hc
    omega

/-- COMPLETENESS POLE: every honest key's nonet satisfies both legs, so the envelope refuses no
honest witness. -/
theorem canonicalKey9_of_encode (b : Bytes32) : CanonicalKey9 (keyToLanes9 b) := by
  refine ⟨fun i _ => keyToLanes9_lt_K b i, ?_⟩
  have hlr : LanesRanged (keyToLanes9 b) := fun i _ => keyToLanes9_lt_K b i
  rw [topLane_iff_decWord_lt hlr, keyDecWord_encode]
  exact keyWord_lt b

/-- **THE IMAGE CHARACTERIZATION.** The two legs are EXACTLY the encoder's image — not a superset
that merely contains it. So there is no third condition left unstated, and an AIR forcing them
admits every honest witness and no off-image one. -/
theorem canonicalKey9_iff_in_image (L : Nonet) :
    CanonicalKey9 L ↔ ∃ b : Bytes32, keyToLanes9 b = L := by
  constructor
  · intro hL
    refine ⟨keyLanes9ToBytes L, ?_⟩
    have hw : keyDecWord L < 2 ^ 256 := (topLane_iff_decWord_lt hL.1).mp hL.2
    have hdig : ∀ x ∈ digitsN 256 32 (keyDecWord L), x < 256 :=
      digitsN_lt 256 (by norm_num) 32 (keyDecWord L)
    have hbytes : keyBytes (keyLanes9ToBytes L) = digitsN 256 32 (keyDecWord L) := by
      have hlen : (digitsN 256 32 (keyDecWord L)).length = 32 := digitsN_length _ _ _
      have hmod : ∀ j < 32, (digitsN 256 32 (keyDecWord L)).getD j 0 % 256
          = (digitsN 256 32 (keyDecWord L)).getD j 0 := by
        intro j hj
        refine Nat.mod_eq_of_lt (hdig _ ?_)
        rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
        exact List.getElem_mem _
      simp only [keyBytes, keyLanes9ToBytes]
      rw [
        hmod 0 (by norm_num), hmod 1 (by norm_num), hmod 2 (by norm_num), hmod 3 (by norm_num),
        hmod 4 (by norm_num), hmod 5 (by norm_num), hmod 6 (by norm_num), hmod 7 (by norm_num),
        hmod 8 (by norm_num), hmod 9 (by norm_num), hmod 10 (by norm_num), hmod 11 (by norm_num),
        hmod 12 (by norm_num), hmod 13 (by norm_num), hmod 14 (by norm_num), hmod 15 (by norm_num),
        hmod 16 (by norm_num), hmod 17 (by norm_num), hmod 18 (by norm_num), hmod 19 (by norm_num),
        hmod 20 (by norm_num), hmod 21 (by norm_num), hmod 22 (by norm_num), hmod 23 (by norm_num),
        hmod 24 (by norm_num), hmod 25 (by norm_num), hmod 26 (by norm_num), hmod 27 (by norm_num),
        hmod 28 (by norm_num), hmod 29 (by norm_num), hmod 30 (by norm_num), hmod 31 (by norm_num)]
      exact list32_eta _ hlen
    have hword : keyWord (keyLanes9ToBytes L) = keyDecWord L := by
      simp only [keyWord, hbytes]
      exact ofDigits_digitsN 256 (by norm_num) 32 (keyDecWord L) (by
        have : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
        omega)
    funext i
    simp only [keyToLanes9, hword]
    have hlanes : digitsN K 9 (keyDecWord L) = keyLaneList L := by
      have := digitsN_ofDigits K (by decide) (keyLaneList L)
        (keyLaneList_lt_of_uniform (canonicalKey9_uniformRanged hL))
      rwa [keyLaneList_length] at this
    rw [hlanes]
    fin_cases i <;> simp [keyLaneList]
  · rintro ⟨b, rfl⟩
    exact canonicalKey9_of_encode b

#assert_axioms topLane_iff_decWord_lt
#assert_axioms canonicalKey9_of_encode
#assert_axioms canonicalKey9_iff_in_image

/-! ### ⚑ THE EXHIBIT — why a UNIFORM nine-lane `< 2^29` lookup is NOT the fix.

`forgedKeyNonet = [0, …, 0, 2^24]`. Every lane is below `2^29`, so it passes the naive uniform
range check on ALL NINE lanes. Its recomposed value is `2^24 · (2^29)^8 = 2^256` exactly — one full
wrap — and the total decoder reads base-256 digits `0..31`, all of which are zero. So it decodes
byte-for-byte to the ALL-ZERO key, which is also what the honest zero key's nonet decodes to, while
being a DIFFERENT committed vector.

⚑ This is the same wound the fields octet had (`forgedLanes = [0,…,0,3·2^24]` passing all seven
`< 2^28` lookups), at a different width, and it is why leg 2 rides a NARROWER table rather than the
lane table. Note what it does NOT assume: nothing about lanes 0..7, no producer honesty. Lane 8
alone. -/

/-- The off-image vector: one wrap in the top lane, nothing else. -/
def forgedKeyNonet : Nonet := ![0, 0, 0, 0, 0, 0, 0, 0, 16777216]

/-- The honest nonet of the all-zero key, for the pair. -/
def honestZeroNonet : Nonet := keyToLanes9 zeroKey

theorem honestZeroNonet_eq : honestZeroNonet = ![0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext i
  simp only [honestZeroNonet, keyToLanes9, keyWord, keyBytes, zeroKey, ofDigits]
  fin_cases i <;> simp [digitsN]

/-- **THE REFUTATION OF THE NAIVE FIX.** `forgedKeyNonet` satisfies the uniform `< 2^29` check on
every lane, is NOT the honest vector, decodes to the honest key anyway, and fails ONLY
`TopLaneRanged`. So an AIR carrying nine lane-width lookups still admits it. -/
theorem uniform_lane_ranges_do_not_force_the_image :
    UniformRanged forgedKeyNonet
    ∧ LanesRanged forgedKeyNonet
    ∧ forgedKeyNonet ≠ honestZeroNonet
    ∧ keyLanes9ToBytes forgedKeyNonet = keyLanes9ToBytes honestZeroNonet
    ∧ ¬ TopLaneRanged forgedKeyNonet
    ∧ ¬ CanonicalKey9 forgedKeyNonet := by
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide⟩
  · rw [honestZeroNonet_eq]; decide
  · rw [honestZeroNonet_eq]
    funext j
    apply Fin.ext
    simp only [keyLanes9ToBytes, keyDecWord, keyLaneList, forgedKeyNonet, ofDigits]
    fin_cases j <;> decide

/-- **THE WRAP, AS TWO NUMBERS.** The forged nonet's recomposed value is `2^256` on the nose — one
full wrap of the byte window — while the honest zero nonet's is `0`. Same 32-byte decode. -/
theorem the_forged_nonet_wraps_exactly_once :
    keyDecWord forgedKeyNonet = 2 ^ 256
    ∧ keyDecWord honestZeroNonet = 0
    ∧ keyLanes9ToBytes forgedKeyNonet = zeroKey := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [honestZeroNonet_eq]; decide
  · funext j
    apply Fin.ext
    simp only [keyLanes9ToBytes, keyDecWord, keyLaneList, forgedKeyNonet, ofDigits, zeroKey]
    fin_cases j <;> decide

#assert_axioms uniform_lane_ranges_do_not_force_the_image
#assert_axioms the_forged_nonet_wraps_exactly_once

/-! ## §5 — THE VERDICT, in one proposition.

Stated together so a reader cannot take the pleasant half. The deployed eight-lane octet does not
determine the owner key even under its exact-image canonicity envelope; the nine-lane replacement
does, under an envelope that is two lookups' worth of width and one lookup's worth of narrowing. -/

/-- **THE VERDICT.** (1) the deployed packer conflates two distinct keys whose octets are canonical;
(2) the nine-lane replacement is injective; (3) its canonicity envelope is exactly its image; and
(4) the naive uniform range check does not reach that envelope. -/
theorem key_octet_verdict :
    (∃ a b : Bytes32, a ≠ b ∧ keyToLanes8 a = keyToLanes8 b ∧ KeyCanonical8 (keyToLanes8 a))
    ∧ Function.Injective keyToLanes9
    ∧ (∀ L : Nonet, CanonicalKey9 L ↔ ∃ b : Bytes32, keyToLanes9 b = L)
    ∧ (∃ L : Nonet, UniformRanged L ∧ ¬ CanonicalKey9 L) := by
  refine ⟨⟨zeroKey, bit6Key, eight_lane_canonicity_is_not_a_repair.1,
      eight_lane_canonicity_is_not_a_repair.2.1, eight_lane_canonicity_is_not_a_repair.2.2.1⟩,
    keyToLanes9_injective, canonicalKey9_iff_in_image,
    ⟨forgedKeyNonet, by decide, by decide⟩⟩

#assert_axioms key_octet_verdict

/-! ### Lean-COMPUTED protocol vectors.

⚑ These are COMPUTED by Lean, not transcribed from a Rust run.

⚠ **CORRECTED 2026-08-01.** This paragraph used to end "There is no Rust twin of `keyToLanes9`
yet — the encoder does not exist on the wire". **That is false and was false when read.**
`commit/src/typed.rs::canonical_32_to_lanes_9` says in its own doc comment that it is "The Rust
mirror of `Dregg2.Circuit.KeyLanes9.keyToLanes9`", with the decoder `lanes_9_to_canonical_32`
beside it and three siblings (`storage/src/commitment.rs`, `cell::commitment`, and the
`commit/tests/key_octet_f2_twins_and_the_hole.rs` harness that diffs all four). A stale "does not
exist" line is worse than no line, because the next reader prices a build that is already done.

✅ **AND THE SECOND HALF OF THAT PARAGRAPH IS NOW STALE TOO, 2026-08-02.** It read: "What
`KeyLanes9` lacks is not a twin but an APPLIED emit face: `Emit/KeyCanonicity9Emit.keyCanonical9At`
is written, proved and geometrically placed, and is appended to NO live member's constraint list."
`keyCanonical9Wire` is applied by `EmitRotationV3.lean` and both wide registry probes; the committed
registries carry **960 lookups at 29 bits and 120 more at 24** (narrow; 912 / 114 wide) where they
carried **zero at 29**. So `CanonicalKey9` — which `canonicalKey9_iff_in_image` proves is exactly
this encoder's image — is an emitted obligation on every rotated member's owner nonet, at both
blocks. -/

def lanes9Of (b : Bytes32) : List Nat := List.ofFn (keyToLanes9 b)
def lanes8Of (b : Bytes32) : List Nat := List.ofFn (keyToLanes8 b)
def bytesOf (b : Bytes32) : List Nat := List.ofFn (fun i => (b i).1)

def ascendingKey : Bytes32 := fun i => ⟨i.1, by omega⟩
def maxKey : Bytes32 := fun _ => ⟨255, by decide⟩

/-! The deployed octet drops bit 6 of byte 3: two distinct keys, one octet. -/
#guard lanes8Of zeroKey = lanes8Of bit6Key
#guard bytesOf zeroKey ≠ bytesOf bit6Key

/-! …and the nonet SEPARATES them, which is the whole point. -/
#guard lanes9Of zeroKey ≠ lanes9Of bit6Key

/-! The all-`0xff` key: every lane saturates at `2^29 − 1` except the top, which lands on
`2^24 − 1` — the exact ceiling leg 2 pins. -/
#guard lanes9Of maxKey = [536870911, 536870911, 536870911, 536870911, 536870911,
                          536870911, 536870911, 536870911, 16777215]

/-! Round-trip on structured input. -/
#guard bytesOf (keyLanes9ToBytes (keyToLanes9 ascendingKey)) = bytesOf ascendingKey
#guard bytesOf (keyLanes9ToBytes (keyToLanes9 maxKey)) = bytesOf maxKey
#guard bytesOf (keyLanes9ToBytes (keyToLanes9 bit6Key)) = bytesOf bit6Key

/-! The exhibit, as numbers: the forged top lane is exactly the honest ceiling, and one above the
largest value leg 2 admits. -/
#guard forgedKeyNonet 8 = 16777216
#guard keyToLanes9 maxKey 8 = 16777215
#guard bytesOf (keyLanes9ToBytes forgedKeyNonet) = bytesOf zeroKey

end Dregg2.Circuit.KeyLanes9
