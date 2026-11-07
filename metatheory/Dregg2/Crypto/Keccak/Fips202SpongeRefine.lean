/-
# `Dregg2.Crypto.Keccak.Fips202SpongeRefine` — the executable SPONGE refines the FIPS 202 sponge.

`Fips202Round.keccakF_refines_spec` proves the executable permutation `Keccak.keccakF` computes
FIPS 202's Keccak-f[1600] under the lane/bit abstraction `Fips202Refine.toSpec`. THIS file lifts
that to the layer above: the executable BYTE-addressed sponge (`Keccak.pad` / `Keccak.absorb` /
`Keccak.squeeze`, which store the rate as `UInt64` lanes and the message as `UInt8`) computes the
BIT-addressed FIPS 202 sponge of `Fips202Sponge` (`pad10*1` / `spongeAbsorb` / `spongeSqueeze`).

The bridge is FIPS 202 §B.1 (`Fips202.bitsOfBytes`: byte `i` supplies bits `8i … 8i+7`, LSB first)
composed with §3.1.2 (`Fips202.bitIdx`: state bit `A[x,y,z]` is string bit `64(5y+x) + z`). Those two
conventions agree on the nose with the executable's storage: byte `i` of a rate block is XORed into
lane `i / 8` at shift `8(i mod 8)`, so its bit `b` is state-string bit `8i + b`.

Everything proven here is a genuine `∀` over ALL messages / states / rates, against the SPEC side of
`Fips202Sponge` — which mentions no `UInt64`, no `Array`, and no executable definition.
-/
import Dregg2.Crypto.Keccak.Fips202Round
import Dregg2.Crypto.Keccak.Fips202Sponge

namespace Dregg2.Crypto.Keccak.Fips202SpongeRefine

open Dregg2.Crypto.Keccak
open Dregg2.Crypto.Keccak.Fips202Refine (laneBit toSpec laneBit_xor)
open Dregg2.Crypto.Keccak.Fips202Round (keccakF_refines_spec keccakRound_size)

/-! ## Primitive bridges -/

/-- Reading a `List`-backed `Array` out of bounds and reading the `List` with a default agree. -/
theorem toArray_getElem! (l : List UInt8) (m : Nat) : l.toArray[m]! = l.getD m 0 := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

/-- **A byte, widened and shifted into a lane, contributes exactly its 8 bits at byte-slot `m`.**
The executable's absorb writes `byte.toUInt64 <<< 8·(i mod 8)`; this says bit `z` of that word is
bit `z mod 8` of the byte when `z` lies in byte-slot `m = i mod 8` of the lane, and `0` otherwise. -/
theorem byteShift_bit (b : UInt8) (m z : Nat) (hm : m < 8) (hz : z < 64) :
    (b.toUInt64 <<< (8 * m).toUInt64).toBitVec.getLsbD z
      = (if z / 8 = m then b.toBitVec.getLsbD (z % 8) else false) := by
  have hlt : 8 * m < UInt64.size := by simp only [UInt64.size]; omega
  have hnat : ((8 * m).toUInt64).toNat = 8 * m := UInt64.toNat_ofNat_of_lt' hlt
  have hsh : ((8 * m).toUInt64.toBitVec % 64).toNat = 8 * m := by
    simp only [BitVec.toNat_umod, UInt64.toNat_toBitVec, hnat,
      show (64 : BitVec 64).toNat = 64 from rfl]
    omega
  simp only [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, hsh,
    UInt8.toBitVec_toUInt64, BitVec.getLsbD_setWidth]
  by_cases h : z / 8 = m
  · rw [if_pos h]
    have h5 : ¬ (z < 8 * m) := by omega
    have h6 : z % 8 < 64 := by omega
    have h3 : z - 8 * m = z % 8 := by omega
    simp [h5, h6, h3, hz]
  · rw [if_neg h]
    by_cases h4 : z < 8 * m
    · simp [h4]
    · rw [BitVec.getLsbD_of_ge b.toBitVec (z - 8 * m) (by omega)]
      simp

/-- `Keccak.keccakF` preserves the 25-lane shape (the 24-fold of `keccakRound_size`). -/
theorem keccakF_size (a : Array UInt64) (ha : a.size = 25) : (keccakF a).size = 25 := by
  unfold keccakF
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure]
  suffices h : ∀ (L : List Nat) (s : Array UInt64), s.size = 25 →
      (L.foldl (fun s i => keccakRound s RC[i]!) s).size = 25 from h _ a ha
  intro L
  induction L with
  | nil => intro s hs; simpa using hs
  | cons hd tl ih => intro s hs; simp only [List.foldl_cons]; exact ih _ (keccakRound_size _ _)

/-- The zero lane array abstracts to the FIPS 202 `0^b` state. -/
theorem toSpec_zero : toSpec (Array.replicate 25 (0 : UInt64)) = Fips202.zeroState := by
  funext x y z
  have : (Array.replicate 25 (0 : UInt64))[x.val + 5 * y.val]! = 0 := by
    have hj : x.val + 5 * y.val < 25 := by have := x.isLt; have := y.isLt; omega
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    rw [if_pos hj]; rfl
  simp [toSpec, laneBit, this, Fips202.zeroState]

/-! ## The absorb inner loop (the byte-into-lane XOR fold) -/

/-- The executable `absorb`'s inner loop over the first `k` bytes of a rate block: XOR byte
`arr[base + i]` into lane `i / 8` at shift `8·(i mod 8)`. -/
def xorBytes (arr : Array UInt8) (base : Nat) (k : Nat) (s : Array UInt64) : Array UInt64 :=
  (List.range' 0 k).foldl
    (fun s i => s.set! (i / 8) (s[i / 8]! ^^^ (arr[base + i]!.toUInt64 <<< (8 * (i % 8)).toUInt64))) s

theorem xorBytes_succ (arr : Array UInt8) (base k : Nat) (s : Array UInt64) :
    xorBytes arr base (k + 1) s
      = (xorBytes arr base k s).set! (k / 8)
          ((xorBytes arr base k s)[k / 8]! ^^^
            (arr[base + k]!.toUInt64 <<< (8 * (k % 8)).toUInt64)) := by
  unfold xorBytes
  rw [List.range'_concat]
  simp [List.foldl_append]

theorem xorBytes_size (arr : Array UInt8) (base k : Nat) (s : Array UInt64) :
    (xorBytes arr base k s).size = s.size := by
  induction k with
  | zero => simp [xorBytes]
  | succ k ih => rw [xorBytes_succ]; simp only [Array.set!, Array.size_setIfInBounds]; exact ih

/-- Reading back the lane just written. -/
theorem set!_get_self (a : Array UInt64) (i : Nat) (v : UInt64) (h : i < a.size) :
    (a.set! i v)[i]! = v := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.set!_eq_setIfInBounds]
  simp [h]

/-- Reading back a lane other than the one written. -/
theorem set!_get_other (a : Array UInt64) (i j : Nat) (v : UInt64) (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.set!_eq_setIfInBounds]
  rw [if_neg h]

/-- **The absorb inner loop, entrywise at the bit level.** After XOR-ing the first `k` bytes of the
block into the state, bit `z` of lane `j` is the original bit XORed with bit `z mod 8` of byte
`8j + z/8` of the block — present exactly when that byte index is `< k`. A genuine `forall` over all
byte arrays, all `base`, all `k`, all 25-lane states, all lanes and all bits. -/
theorem xorBytes_bit (arr : Array UInt8) (base k : Nat) (s : Array UInt64) (hs : s.size = 25)
    (j : Nat) (hj : j < 25) (z : Fin 64) :
    laneBit ((xorBytes arr base k s)[j]!) z
      = xor (laneBit (s[j]!) z)
          (if 8 * j + z.val / 8 < k then
              (arr[base + (8 * j + z.val / 8)]!).toBitVec.getLsbD (z.val % 8)
           else false) := by
  have hz : z.val < 64 := z.isLt
  induction k with
  | zero => simp [xorBytes]
  | succ k ih =>
    rw [xorBytes_succ]
    have hFs : (xorBytes arr base k s).size = 25 := by rw [xorBytes_size]; exact hs
    have hbs : laneBit (arr[base + k]!.toUInt64 <<< (8 * (k % 8)).toUInt64) z
        = if z.val / 8 = k % 8 then (arr[base + k]!).toBitVec.getLsbD (z.val % 8) else false :=
      byteShift_bit _ _ _ (Nat.mod_lt _ (by decide)) hz
    by_cases hjk : j = k / 8
    · subst hjk
      rw [set!_get_self _ _ _ (by omega), laneBit_xor, ih, hbs]
      rcases Nat.lt_trichotomy (z.val / 8) (k % 8) with hc | hc | hc
      · rw [if_pos (show 8 * (k / 8) + z.val / 8 < k by omega),
            if_neg (show ¬ (z.val / 8 = k % 8) by omega),
            if_pos (show 8 * (k / 8) + z.val / 8 < k + 1 by omega)]
        simp
      · rw [if_neg (show ¬ (8 * (k / 8) + z.val / 8 < k) by omega),
            if_pos (show z.val / 8 = k % 8 from hc),
            if_pos (show 8 * (k / 8) + z.val / 8 < k + 1 by omega),
            show 8 * (k / 8) + z.val / 8 = k by omega]
        simp
      · rw [if_neg (show ¬ (8 * (k / 8) + z.val / 8 < k) by omega),
            if_neg (show ¬ (z.val / 8 = k % 8) by omega),
            if_neg (show ¬ (8 * (k / 8) + z.val / 8 < k + 1) by omega)]
        simp
    · rw [set!_get_other _ _ _ _ (fun h => hjk h.symm), ih]
      have hz8 : z.val / 8 < 8 := by omega
      by_cases hc : 8 * j + z.val / 8 < k
      · rw [if_pos hc, if_pos (show 8 * j + z.val / 8 < k + 1 by omega)]
      · rw [if_neg hc, if_neg (show ¬ (8 * j + z.val / 8 < k + 1) by omega)]

/-! ## The absorb block refinement -/

/-- **One absorb block refines FIPS 202 Algorithm 8 step 6's `S ⊕ (P_i || 0^c)`.** For EVERY byte
list, EVERY block index, EVERY rate and EVERY 25-lane state: XOR-ing the `rate` bytes of block `blk`
into the lanes is, under `toSpec`, XOR-ing the FIPS 202 `8·rate`-bit block `P_blk` (zero-extended
over the capacity) into the bit-addressed state. -/
theorem xorBytes_refines (bs : List UInt8) (blk rate : Nat) (s : Array UInt64) (hs : s.size = 25) :
    toSpec (xorBytes bs.toArray (blk * rate) rate s)
      = Fips202.xorBlock (toSpec s) (Fips202.blockAt (8 * rate) (Fips202.bitsOfBytes bs) blk) := by
  funext x y z
  have hx : x.val < 5 := x.isLt
  have hy : y.val < 5 := y.isLt
  have hz : z.val < 64 := z.isLt
  have hj : x.val + 5 * y.val < 25 := by omega
  simp only [toSpec]
  rw [xorBytes_bit _ _ _ _ hs _ hj z]
  simp only [Fips202.xorBlock, toSpec, Fips202.blockAt_getD, Fips202.bitsOfBytes_getD,
    Fips202.bitIdx, toArray_getElem!]
  have hb : blk * (8 * rate) = 8 * (blk * rate) := by
    rw [← Nat.mul_assoc, Nat.mul_comm blk 8, Nat.mul_assoc]
  rw [hb]
  refine congrArg _ ?_
  by_cases hcond : 64 * (5 * y.val + x.val) + z.val < 8 * rate
  · rw [if_pos (show 8 * (x.val + 5 * y.val) + z.val / 8 < rate by omega), if_pos hcond,
      show blk * rate + (8 * (x.val + 5 * y.val) + z.val / 8)
          = (8 * (blk * rate) + (64 * (5 * y.val + x.val) + z.val)) / 8 by omega,
      show z.val % 8 = (8 * (blk * rate) + (64 * (5 * y.val + x.val) + z.val)) % 8 by omega]
  · rw [if_neg (show ¬ (8 * (x.val + 5 * y.val) + z.val / 8 < rate) by omega), if_neg hcond]

/-! ## The absorb fold -/

/-- The block fold: absorbing a list of block indices refines the FIPS 202 absorb fold, given the
lane/bit abstraction relates the starting states. Composes `xorBytes_refines` (one block) with
`keccakF_refines_spec` (the permutation between blocks). -/
theorem absorb_fold (bs : List UInt8) (rate : Nat) :
    ∀ (L : List Nat) (s : Array UInt64), s.size = 25 →
      toSpec (L.foldl (fun s blk => keccakF (xorBytes bs.toArray (blk * rate) rate s)) s)
        = L.foldl (fun S blk =>
            Fips202.keccakF (Fips202.xorBlock S
              (Fips202.blockAt (8 * rate) (Fips202.bitsOfBytes bs) blk))) (toSpec s) := by
  intro L
  induction L with
  | nil => intro s _; simp
  | cons hd tl ih =>
    intro s hs
    simp only [List.foldl_cons]
    have h1 : (xorBytes bs.toArray (hd * rate) rate s).size = 25 := by
      rw [xorBytes_size]; exact hs
    rw [ih _ (keccakF_size _ h1), keccakF_refines_spec _ h1, xorBytes_refines bs hd rate s hs]

/-- The executable `absorb` as an explicit fold (the `Id.run` loops normalized). -/
theorem absorb_eq (rate : Nat) (padded : List UInt8) :
    absorb rate padded =
      (List.range' 0 (padded.toArray.size / rate)).foldl
        (fun s blk => keccakF (xorBytes padded.toArray (blk * rate) rate s))
        (Array.replicate 25 0) := by
  unfold absorb xorBytes
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- **THE ABSORB REFINEMENT (proven).** For EVERY rate `> 0` and EVERY padded byte string, the
executable `Keccak.absorb` computes, under the lane/bit abstraction `toSpec`, exactly the FIPS 202
§4 Algorithm 8 absorb phase (steps 5–6) at rate `8·rate` bits over the §B.1 bit string of the
bytes. -/
theorem absorb_refines_spec (rate : Nat) (padded : List UInt8) :
    toSpec (absorb rate padded)
      = Fips202.spongeAbsorb (8 * rate) (Fips202.bitsOfBytes padded) := by
  rw [absorb_eq]
  have hlen : (Fips202.bitsOfBytes padded).length / (8 * rate) = padded.toArray.size / rate := by
    rw [Fips202.bitsOfBytes_length, List.size_toArray, Nat.mul_div_mul_left _ _ (by decide)]
  simp only [Fips202.spongeAbsorb, hlen, List.range_eq_range']
  rw [← toSpec_zero]
  exact absorb_fold padded rate _ _ (by simp)

/-! ## The padding refinement (FIPS 202 §5.1 `pad10*1` + the §6.2 SHAKE domain bits `1111`) -/

/-- Zero bytes are zero bits. -/
theorem bitsOfBytes_replicate_zero (n : Nat) :
    Fips202.bitsOfBytes (List.replicate n 0) = List.replicate (8 * n) false := by
  induction n with
  | zero => simp [Fips202.bitsOfBytes]
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [Fips202.bitsOfBytes, List.flatMap_cons] at *
    rw [show Fips202.bitsOfByte 0 = List.replicate 8 false from by decide, ih,
      List.replicate_append_replicate]
    congr 1
    omega

/-- **The `pad10*1` bit count.** For the executable's byte pad count `q = rate − (|msg| mod rate)`,
FIPS 202 §5.1's `j = (−m − 2) mod x` at `x = 8·rate`, `m = 8·|msg| + 4` (the message bits plus the
four SHAKE domain bits `1111`) is exactly `8q − 6`. -/
theorem pad10s1_bits (rate L : Nat) (hr : 0 < rate) :
    Fips202.pad10s1 (8 * rate) (8 * L + 4)
      = true :: (List.replicate (8 * (rate - L % rate) - 6) false ++ [true]) := by
  have hm : L % rate < rate := Nat.mod_lt _ hr
  have hk : rate * (L / rate) + L % rate = L := Nat.div_add_mod L rate
  have hassoc : (8 * rate) * (L / rate) = 8 * (rate * (L / rate)) := by rw [Nat.mul_assoc]
  have h1 : 8 * L + 4 + 2 = (8 * rate) * (L / rate) + (8 * (L % rate) + 6) := by omega
  unfold Fips202.pad10s1
  rw [h1, Nat.mul_add_mod,
    Nat.mod_eq_of_lt (show 8 * (L % rate) + 6 < 8 * rate by omega),
    Nat.mod_eq_of_lt (show 8 * rate - (8 * (L % rate) + 6) < 8 * rate by omega),
    show 8 * rate - (8 * (L % rate) + 6) = 8 * (rate - L % rate) - 6 by omega]

/-- **THE PADDING REFINEMENT (proven).** For EVERY rate `> 0` and EVERY message, the executable
`Keccak.pad` — which appends the SHAKE domain byte `0x1F`, zero bytes, and a `0x80` terminator (or
the single collapsed byte `0x9F`) — produces exactly the FIPS 202 §B.1 bit string of the message,
followed by the §6.2 SHAKE domain bits `1111`, followed by FIPS 202 §5.1's `pad10*1(8·rate, ·)`.
This is the theorem that pins the `0x1F` / `0x80` / `0x9F` byte encoding to the STANDARD's padding,
including the one-byte collapse branch. -/
theorem pad_refines_spec (rate : Nat) (hr : 0 < rate) (msg : List UInt8) :
    Fips202.bitsOfBytes (pad rate msg)
      = Fips202.bitsOfBytes msg ++ [true, true, true, true]
          ++ Fips202.pad10s1 (8 * rate) (8 * msg.length + 4) := by
  have hm : msg.length % rate < rate := Nat.mod_lt _ hr
  rw [pad10s1_bits rate msg.length hr]
  unfold pad
  by_cases hq : (rate - msg.length % rate) == 1
  · have hq1 : rate - msg.length % rate = 1 := by simpa using hq
    rw [if_pos hq, hq1, show (8 * 1 - 6) = 2 from rfl, Fips202.bitsOfBytes_append,
      show Fips202.bitsOfBytes [0x9F]
          = [true, true, true, true] ++ (true :: (List.replicate 2 false ++ [true]))
        from by decide]
    simp [List.append_assoc]
  · have hq2 : 2 ≤ rate - msg.length % rate := by
      have : ¬ (rate - msg.length % rate = 1) := by simpa using hq
      omega
    rw [if_neg hq]
    simp only [Fips202.bitsOfBytes, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [show Fips202.bitsOfByte 0x1F
          = [true, true, true, true, true] ++ List.replicate 3 false from by decide,
      show Fips202.bitsOfByte 0x80 = List.replicate 7 false ++ [true] from by decide,
      show (List.replicate (rate - msg.length % rate - 2) (0 : UInt8)).flatMap Fips202.bitsOfByte
          = List.replicate (8 * (rate - msg.length % rate - 2)) false
        from bitsOfBytes_replicate_zero _]
    have hsplit : List.replicate (8 * (rate - msg.length % rate) - 6) false ++ [true]
        = List.replicate 3 false ++ (List.replicate (8 * (rate - msg.length % rate - 2)) false
            ++ (List.replicate 7 false ++ [true])) := by
      rw [show 8 * (rate - msg.length % rate) - 6
            = 3 + 8 * (rate - msg.length % rate - 2) + 7 by omega,
        ← List.replicate_append_replicate, ← List.replicate_append_replicate,
        List.append_assoc, List.append_assoc]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hsplit]

/-- **The padded message is a whole number of rate blocks.** This is what makes FIPS 202 Algorithm 8
step 2's `n = len(P) / r` an exact block decomposition rather than a truncation, on both sides of
the absorb refinement. -/
theorem pad_length_multiple (rate : Nat) (hr : 0 < rate) (msg : List UInt8) :
    (pad rate msg).length % rate = 0 := by
  have hm : msg.length % rate < rate := Nat.mod_lt _ hr
  have hk := Nat.div_add_mod msg.length rate
  have hmul : rate * (msg.length / rate + 1) = rate * (msg.length / rate) + rate := by
    rw [Nat.mul_succ]
  unfold pad
  by_cases hq : (rate - msg.length % rate) == 1
  · have hq1 : rate - msg.length % rate = 1 := by simpa using hq
    rw [if_pos hq]
    simp only [List.length_append, List.length_singleton]
    rw [show msg.length + 1 = rate * (msg.length / rate + 1) by omega, Nat.mul_mod_right]
  · have hq2 : 2 ≤ rate - msg.length % rate := by
      have : ¬ (rate - msg.length % rate = 1) := by simpa using hq
      omega
    rw [if_neg hq]
    simp only [List.length_append, List.length_cons, List.length_replicate, List.length_nil]
    rw [show msg.length + (rate - msg.length % rate - 2 + 1) + (0 + 1)
          = rate * (msg.length / rate + 1) by omega, Nat.mul_mod_right]

/-! ## The squeeze refinement (FIPS 202 §4 Algorithm 8 steps 7–10) -/

/-- Two equal-length bit strings that agree at every in-range index are equal. -/
theorem list_ext_getD (l l' : List Bool) (hlen : l.length = l'.length)
    (h : ∀ i, i < l.length → l.getD i false = l'.getD i false) : l = l' := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have hg : l.getD i false = l[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  have hg' : l'.getD i false = l'[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
  rw [← hg, ← hg']
  exact h i h1

/-- Indexing a `map` over `List.range'` inside its range. -/
theorem getD_map_range' {α} (f : Nat → α) (n i : Nat) (d : α) (h : i < n) :
    ((List.range' 0 n).map f).getD i d = f i := by
  rw [← List.range_eq_range', List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range h]
  simp

/-- **A lane byte, read back at a byte slot, is that slice of the lane's bits.** Dual of
`byteShift_bit`: the executable's squeeze emits `(lane >>> 8·(i mod 8)).toUInt8`. -/
theorem laneByte_bit (w : UInt64) (m b : Nat) (hm : m < 8) (hb : b < 8) :
    ((w >>> (8 * m).toUInt64).toUInt8).toBitVec.getLsbD b = w.toBitVec.getLsbD (8 * m + b) := by
  have hlt : 8 * m < UInt64.size := by simp only [UInt64.size]; omega
  have hnat : ((8 * m).toUInt64).toNat = 8 * m := UInt64.toNat_ofNat_of_lt' hlt
  have hsh : ((8 * m).toUInt64.toBitVec % 64).toNat = 8 * m := by
    simp only [BitVec.toNat_umod, UInt64.toNat_toBitVec, hnat,
      show (64 : BitVec 64).toNat = 64 from rfl]
    omega
  simp only [UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt64.toBitVec_shiftRight,
    BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, hsh, hb, decide_true, Bool.true_and]

/-- One squeezed rate block of bytes, as the executable emits it. -/
def blockBytes (rate : Nat) (s : Array UInt64) : List UInt8 :=
  (List.range' 0 rate).map (fun i => (s[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8)

@[simp] theorem blockBytes_length (rate : Nat) (s : Array UInt64) :
    (blockBytes rate s).length = rate := by simp [blockBytes]

/-- **One squeezed block refines FIPS 202 Algorithm 8 step 8's `Trunc_r(S)`.** For every 25-lane
state and every rate up to the 200-byte state width, the `rate` bytes the executable reads out are,
under §B.1 and §3.1.2, exactly the first `8·rate` bits of the state string. -/
theorem blockBytes_bits (rate : Nat) (s : Array UInt64) (hrate : 8 * rate ≤ 1600) :
    Fips202.bitsOfBytes (blockBytes rate s) = Fips202.truncR (8 * rate) (toSpec s) := by
  refine list_ext_getD _ _ (by simp [Fips202.truncR]) ?_
  intro k hk
  rw [Fips202.bitsOfBytes_length, blockBytes_length] at hk
  have hk8 : k / 8 < rate := by omega
  have h64 : k / 64 < 25 := by omega
  rw [Fips202.bitsOfBytes_getD, blockBytes, getD_map_range' _ _ _ _ hk8,
    laneByte_bit _ _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
  rw [List.getD_eq_getElem?_getD, Fips202.truncR, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some, Fips202.stateBit, toSpec, laneBit]
  simp only [Fips202.m5]
  rw [show k / 8 / 8 = k / 64 % 5 + 5 * (k / 64 / 5 % 5) by omega,
    show 8 * (k / 8 % 8) + k % 8 = k % 64 by omega]

/-- The executable squeeze's outer loop step (`out` and the state, as the `do`-block pair). -/
def sqStep (rate nblocks : Nat) (b : MProd (Array UInt8) (Array UInt64)) (blk : Nat) :
    MProd (Array UInt8) (Array UInt64) :=
  if blk + 1 < nblocks then
    ⟨(List.range' 0 rate).foldl
        (fun o a => o.push (b.snd[a / 8]! >>> (8 * (a % 8)).toUInt64).toUInt8) b.fst, keccakF b.snd⟩
  else
    ⟨(List.range' 0 rate).foldl
        (fun o a => o.push (b.snd[a / 8]! >>> (8 * (a % 8)).toUInt64).toUInt8) b.fst, b.snd⟩

/-- The executable `squeeze` as an explicit fold (the `Id.run` loops normalized). -/
theorem squeeze_eq (rate : Nat) (s0 : Array UInt64) (outLen : Nat) :
    squeeze rate s0 outLen =
      (((List.range' 0 ((outLen + rate - 1) / rate)).foldl
          (sqStep rate ((outLen + rate - 1) / rate)) ⟨#[], s0⟩).fst.toList).take outLen := by
  -- v4.35 threads the loop state as the `Prod` `(state, out)`; `sqStep` is the `MProd ⟨out, state⟩`.
  have H : ∀ (x : MProd (Array UInt8) (Array UInt64)) (blk : Nat),
      (fun (st : Array UInt64 × Array UInt8) (blk : Nat) =>
          if blk + 1 < (outLen + rate - 1) / rate then
            (keccakF st.1, (List.range' 0 rate).foldl
              (fun o a => o.push (st.1[a / 8]! >>> (8 * (a % 8)).toUInt64).toUInt8) st.2)
          else
            (st.1, (List.range' 0 rate).foldl
              (fun o a => o.push (st.1[a / 8]! >>> (8 * (a % 8)).toUInt64).toUInt8) st.2))
        ((fun p : MProd (Array UInt8) (Array UInt64) => ((p.2, p.1) : Array UInt64 × Array UInt8)) x)
        blk
      = (fun p : MProd (Array UInt8) (Array UInt64) => ((p.2, p.1) : Array UInt64 × Array UInt8))
          (sqStep rate ((outLen + rate - 1) / rate) x blk) := by
    intro x blk
    by_cases h : blk + 1 < (outLen + rate - 1) / rate <;> simp [sqStep, h]
  unfold squeeze
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure, pure_bind,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← apply_ite (f := fun (p : Array UInt64 × Array UInt8) => ForInStep.yield p),
    ← apply_ite (f := fun (p : ForInStep (Array UInt64 × Array UInt8)) => (pure p : Id _)),
    List.forIn_pure_yield_eq_foldl]
  rw [List.foldl_hom
    (fun p : MProd (Array UInt8) (Array UInt64) => ((p.2, p.1) : Array UInt64 × Array UInt8))
    (init := ⟨#[], s0⟩) H]
  rfl

/-- The bytes the executable squeezes out of `n` blocks (permuting between blocks). -/
def execBlocks (rate : Nat) : Nat → Array UInt64 → List UInt8
  | 0, _ => []
  | n + 1, s => blockBytes rate s ++ execBlocks rate n (keccakF s)

/-- The squeeze outer loop emits exactly `execBlocks`: `cnt` blocks with `Keccak-f` between them
(and none after the last, which is where `blk + 1 < nblocks` matters). -/
theorem squeeze_fold (rate nblocks : Nat) :
    ∀ (cnt start : Nat), start + cnt = nblocks →
      ∀ (s : Array UInt64) (out : Array UInt8),
        (((List.range' start cnt).foldl (sqStep rate nblocks) ⟨out, s⟩).fst).toList
          = out.toList ++ execBlocks rate cnt s := by
  intro cnt
  induction cnt with
  | zero => intro start _ s out; simp [execBlocks]
  | succ k ih =>
    intro start hstart s out
    rw [show List.range' start (k + 1) = start :: List.range' (start + 1) k from rfl,
      List.foldl_cons]
    by_cases hk : k = 0
    · subst hk
      have hcond : ¬ (start + 1 < nblocks) := by omega
      simp only [sqStep, if_neg hcond]
      rw [ih (start + 1) (by omega)]
      simp [execBlocks, blockBytes]
    · have hcond : start + 1 < nblocks := by omega
      simp only [sqStep, if_pos hcond]
      rw [ih (start + 1) (by omega)]
      simp [execBlocks, blockBytes, List.append_assoc]

/-- **The squeezed blocks refine FIPS 202 Algorithm 8 steps 7–9.** Composes `blockBytes_bits`
(one `Trunc_r`) with `keccakF_refines_spec` (the permutation between blocks). -/
theorem execBlocks_bits (rate : Nat) (hrate : 8 * rate ≤ 1600) :
    ∀ (n : Nat) (s : Array UInt64), s.size = 25 →
      Fips202.bitsOfBytes (execBlocks rate n s)
        = Fips202.squeezeBlocks (8 * rate) n (toSpec s) := by
  intro n
  induction n with
  | zero => intro s _; simp [execBlocks, Fips202.squeezeBlocks, Fips202.bitsOfBytes]
  | succ n ih =>
    intro s hs
    rw [execBlocks, Fips202.bitsOfBytes_append, blockBytes_bits rate s hrate,
      ih (keccakF s) (keccakF_size s hs), keccakF_refines_spec s hs]
    rfl

/-- Taking past a prefix. -/
theorem take_append_len {α} : ∀ (A B : List α) (n : Nat),
    (A ++ B).take (A.length + n) = A ++ B.take n
  | [], B, n => by simp
  | a :: A, B, n => by
    simp only [List.cons_append, List.length_cons,
      show A.length + 1 + n = (A.length + n) + 1 by omega, List.take_succ_cons,
      take_append_len A B n]

/-- Truncating the byte output truncates the bit string eight times as far. -/
theorem bitsOfBytes_take (l : List UInt8) (n : Nat) :
    Fips202.bitsOfBytes (l.take n) = (Fips202.bitsOfBytes l).take (8 * n) := by
  induction l generalizing n with
  | nil => simp [Fips202.bitsOfBytes]
  | cons b l ih =>
    cases n with
    | zero => simp [Fips202.bitsOfBytes]
    | succ m =>
      simp only [List.take_succ_cons, Fips202.bitsOfBytes, List.flatMap_cons]
      rw [show 8 * (m + 1) = (Fips202.bitsOfByte b).length + 8 * m by
            rw [Fips202.bitsOfByte_length]; omega,
        take_append_len]
      exact congrArg _ (ih m)

/-- The executable's block count (in bytes) is the FIPS 202 block count (in bits). -/
theorem numBlocks_bytes (rate outLen : Nat) (hr : 0 < rate) :
    Fips202.numBlocks (8 * rate) (8 * outLen) = (outLen + rate - 1) / rate := by
  have hx := Nat.div_add_mod (outLen + rate - 1) rate
  have hm := Nat.mod_lt (outLen + rate - 1) hr
  have hassoc : (8 * rate) * ((outLen + rate - 1) / rate)
      = 8 * (rate * ((outLen + rate - 1) / rate)) := by rw [Nat.mul_assoc]
  simp only [Fips202.numBlocks]
  rw [show 8 * outLen + 8 * rate - 1
        = (8 * rate) * ((outLen + rate - 1) / rate) + (8 * ((outLen + rate - 1) % rate) + 7)
      by omega,
    Nat.mul_add_div (by omega),
    Nat.div_eq_of_lt (show 8 * ((outLen + rate - 1) % rate) + 7 < 8 * rate by omega),
    Nat.add_zero]

/-- **THE SQUEEZE REFINEMENT (proven).** For EVERY rate with `0 < rate ≤ 200` (the state is 200
bytes), EVERY 25-lane state and EVERY output length, the executable `Keccak.squeeze` emits exactly
the §B.1 bit string of the FIPS 202 §4 Algorithm 8 squeeze phase at rate `8·rate` bits. -/
theorem squeeze_refines_spec (rate : Nat) (hr : 0 < rate) (hrate : 8 * rate ≤ 1600)
    (s0 : Array UInt64) (hs : s0.size = 25) (outLen : Nat) :
    Fips202.bitsOfBytes (squeeze rate s0 outLen)
      = Fips202.spongeSqueeze (8 * rate) (toSpec s0) (8 * outLen) := by
  rw [squeeze_eq, bitsOfBytes_take,
    squeeze_fold rate ((outLen + rate - 1) / rate) ((outLen + rate - 1) / rate) 0 (by omega) s0 #[]]
  simp only [List.nil_append]
  rw [execBlocks_bits rate hrate _ s0 hs, Fips202.spongeSqueeze, numBlocks_bytes rate outLen hr]

/-! ## The whole sponge: the executable SHAKE refines FIPS 202 §6.2 -/

theorem absorb_size (rate : Nat) (padded : List UInt8) : (absorb rate padded).size = 25 := by
  rw [absorb_eq]
  suffices h : ∀ (L : List Nat) (s : Array UInt64), s.size = 25 →
      (L.foldl (fun s blk => keccakF (xorBytes padded.toArray (blk * rate) rate s)) s).size = 25
    from h _ _ (by simp)
  intro L
  induction L with
  | nil => intro s hs; simpa using hs
  | cons hd tl ih =>
    intro s hs
    simp only [List.foldl_cons]
    exact ih _ (keccakF_size _ (by rw [xorBytes_size]; exact hs))

/-- The executable padded message, as the FIPS 202 §4 step-1 padded bit string of the message bits
followed by the §6.2 SHAKE domain bits `1111`. -/
theorem pad_as_padded (rate : Nat) (hr : 0 < rate) (input : List UInt8) :
    Fips202.bitsOfBytes (pad rate input)
      = Fips202.padded (8 * rate)
          (Fips202.bitsOfBytes input ++ [true, true, true, true]) := by
  rw [pad_refines_spec rate hr input]
  simp only [Fips202.padded, List.append_assoc, List.length_append, Fips202.bitsOfBytes_length,
    List.length_cons, List.length_nil]

/-- **THE SPONGE REFINEMENT — SHAKE256 (proven).** For EVERY input byte string and EVERY output
length, the executable `Keccak.shake256` produces exactly the bytes whose FIPS 202 §B.1 bit string is
FIPS 202 §6.2's `SHAKE256(M, 8·outLen)` of the input's bit string. Composes the padding, absorb and
squeeze refinements over `keccakF_refines_spec`. -/
theorem shake256_refines_SHAKE256 (input : List UInt8) (outLen : Nat) :
    Fips202.bitsOfBytes (shake256 input outLen)
      = Fips202.SHAKE256 (Fips202.bitsOfBytes input) (8 * outLen) := by
  unfold shake256 Fips202.SHAKE256 Fips202.keccakC Fips202.sponge
  rw [squeeze_refines_spec 136 (by decide) (by decide) _ (absorb_size _ _) outLen,
    absorb_refines_spec 136 (pad 136 input), pad_as_padded 136 (by decide) input,
    show (8 : Nat) * 136 = 1600 - 512 from rfl]

/-- **THE SPONGE REFINEMENT — SHAKE128 (proven).** As above at rate 168 bytes = 1344 bits. -/
theorem shake128_refines_SHAKE128 (input : List UInt8) (outLen : Nat) :
    Fips202.bitsOfBytes (shake128 input outLen)
      = Fips202.SHAKE128 (Fips202.bitsOfBytes input) (8 * outLen) := by
  unfold shake128 Fips202.SHAKE128 Fips202.keccakC Fips202.sponge
  rw [squeeze_refines_spec 168 (by decide) (by decide) _ (absorb_size _ _) outLen,
    absorb_refines_spec 168 (pad 168 input), pad_as_padded 168 (by decide) input,
    show (8 : Nat) * 168 = 1600 - 256 from rfl]

/-- **`Fips202Refine.SpongeRefinesObligation` — DISCHARGED.** The last open Keccak-floor obligation
stated in `Fips202Refine` (a `True` placeholder while no FIPS 202 sponge specification existed) is
now a real proposition against `Fips202Sponge`, and this is its proof. -/
theorem sponge_refines : Fips202Refine.SpongeRefinesObligation :=
  ⟨shake256_refines_SHAKE256, shake128_refines_SHAKE128⟩

/-! ## Anti-vacuity: the SPEC sponge reproduces a NIST CAVP vector

The refinement theorems above say the executable AGREES with the spec. That is only worth something
if the spec is the real SHAKE — so here is the spec's own output on the FIPS 202 anchor, obtained by
transporting the executable's CAVP-cited KAT (`Keccak.shake256_empty_kat`, NIST CAVP
`SHAKE256ShortMsg.rsp` `Len = 0`) ACROSS the refinement. It inherits that KAT's `native_decide`
residual; it is stated as a witness that the bit-addressed sponge spec is not vacuous, not as a
`forall`. -/

/-- The FIPS 202 sec. 6.2 SPEC sponge, on the empty message, emits the 256 bits of the NIST CAVP
`SHAKE256("")` answer. -/
theorem spec_SHAKE256_empty_cavp :
    Fips202.SHAKE256 [] 256
      = Fips202.bitsOfBytes
          [0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13,
           0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb, 0x24,
           0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82,
           0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5, 0x76, 0x2f] := by
  have h := shake256_refines_SHAKE256 [] 32
  rw [shake256_empty_kat] at h
  simpa [Fips202.bitsOfBytes] using h.symm

end Dregg2.Crypto.Keccak.Fips202SpongeRefine
