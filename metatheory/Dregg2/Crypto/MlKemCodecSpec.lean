/-
# `Dregg2.Crypto.MlKemCodecSpec` — the ML-KEM byte codec round-trip `byteDecode ∘ byteEncode = id`, ∀.

`MlKemCodec` proved `ek_roundtrip` / `ct_roundtrip` only on the pinned REAL crate bytes (`native_decide`).
This module closes the ∀-level codec identity the `DecapsCoreSpec` / `EncapsCoreSpec` residuals name — the
"byte-level `byteDecode ∘ byteEncode = id` structured-value recovery" — as a GENUINE positional-`Nat`-digit
proof (the ML-KEM analog of `VerifyCoreEqSpec.unpackBits_packBits`):

* **`byteDecodeAt_byteEncode`** — for a size-256 coefficient array whose entries are all below the codec's
  effective modulus (`2ᵈ` for the compressed widths `d < 12`, `q = 3329` for the `d = 12`
  `ByteEncode₁₂/ByteDecode₁₂` NTT-domain widths), `byteDecodeAt d (byteEncode d f).toArray 0 = f`.
  Instantiated at the four ML-KEM widths: `d = 12` (`t̂`/`ŝ`), `du = 10` (`u`), `dv = 4` (`v`), `d = 1`
  (the message) — `byteDecode₁₂_byteEncode₁₂`, `byteDecode_du_..`, `byteDecode_dv_..`, `byteDecode₁_byteEncode₁`.

The chain is pure computable-`Nat` arithmetic through the `Id.run do` accumulate/emit and read/`set!` loops:
`accFold` (little-endian mixed-radix accumulate), `divPushFold_spec` (the base-`256` emit), `setFold_spec` (the
base-`2ᵈ` indexed unpack), and the base-`b` positional-numeral facts (`digit_reconstruct`, `digit_bound`,
`extract_digit`) — the SAME engine `VerifyCoreEqSpec` used for ML-DSA, re-derived here over the ML-KEM codec's
own big-`Nat` (un)packer. NO `native_decide` in any `∀`, NO hardness, NO framework gap.

## NON-FAKE

Every `∀`-theorem is `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `native_decide` in
any `∀`-body. Non-vacuity: `byteDecode₁₂_byteEncode₁₂_witness` fires on a genuine `< q` NTT-domain poly.
-/
import Dregg2.Crypto.MlKemCodec
import Dregg2.Tactics
import Mathlib

namespace Dregg2.Crypto.MlKemCodecSpec

open Dregg2.Crypto.MlKemRing (Poly q zeroPoly)
open Dregg2.Crypto.MlKemCodec (bytesToNatLE byteEncode byteDecodeAt byteDecode polyBytes dCoeff du dv)

set_option maxRecDepth 8000

/-- `zeroPoly` reads `0` at every in-range slot. -/
theorem zeroPoly_get (j : Nat) (hj : j < 256) : zeroPoly[j]! = 0 := by
  have hs : j < zeroPoly.size := by simpa [zeroPoly] using hj
  rw [getElem!_pos zeroPoly j hs]; simp [zeroPoly]

/-! ## Generic positional-numeral engine (re-derived over the ML-KEM codec's own big-`Nat` (un)packer). -/

/-- Generic accumulate fold (do-notation `MProd` state): `st.1 += g a * st.2 ; st.2 *= D`. -/
theorem accFold (g : Nat → Nat) (D : Nat) :
    ∀ (n : Nat) (A m : Nat),
      List.foldl (fun (st : MProd Nat Nat) (a : Nat) => ⟨st.1 + g a * st.2, st.2 * D⟩)
          ⟨A, m⟩ (List.range' 0 n 1)
        = ⟨A + m * ∑ i ∈ Finset.range n, g i * D ^ i, m * D ^ n⟩ := by
  intro n
  induction n with
  | zero => intro A m; simp
  | succ k ih =>
    intro A m
    rw [List.range'_1_concat, List.foldl_concat, ih]
    simp only [Nat.zero_add, Finset.sum_range_succ, pow_succ, MProd.mk.injEq]
    exact ⟨by ring, by ring⟩

theorem getElem!_push_lt {β} [Inhabited β] (arr : Array β) (x : β) (i : Nat) (h : i < arr.size) :
    (arr.push x)[i]! = arr[i]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push,
    if_neg (Nat.ne_of_lt h)]

theorem getElem!_push_eq {β} [Inhabited β] (arr : Array β) (x : β) :
    (arr.push x)[arr.size]! = x := by simp

/-- `set!` at an index other than `j` leaves slot `j` unchanged. -/
theorem getElem!_set!_ne {β} [Inhabited β] (arr : Array β) (i : Nat) (v : β) (j : Nat) (h : i ≠ j) :
    (arr.set! i v)[j]! = arr[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_ne h]

/-- `set!` at an in-bounds index `i` writes `v` at slot `i`. -/
theorem getElem!_set!_self {β} [Inhabited β] (arr : Array β) (i : Nat) (v : β) (h : i < arr.size) :
    (arr.set! i v)[i]! = v := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt h, Option.getD_some]

theorem size_mkEmpty {β} (n : Nat) : (Array.mkEmpty (α := β) n).size = 0 :=
  Array.isEmpty_iff_size_eq_zero.mp rfl

/-- Generic push/divide fold spec (do-notation `MProd ⟨cur, out⟩` state): emit `f (cur % D)`, `cur /= D`. -/
theorem divPushFold_spec {β} [Inhabited β] (f : Nat → β) (D : Nat) :
    ∀ (n : Nat) (init : Array β) (c0 : Nat),
      let r := List.foldl (fun (st : MProd Nat (Array β)) (_ : Nat) =>
                 ⟨st.1 / D, st.2.push (f (st.1 % D))⟩) ⟨c0, init⟩ (List.range' 0 n 1)
      r.1 = c0 / D ^ n ∧ r.2.size = init.size + n ∧
        (∀ j, j < init.size → r.2[j]! = init[j]!) ∧
        (∀ j, j < n → r.2[init.size + j]! = f (c0 / D ^ j % D)) := by
  intro n
  induction n with
  | zero => intro init c0; simp
  | succ k ih =>
    intro init c0
    rw [List.range'_1_concat, List.foldl_concat]
    obtain ⟨h1, hsz, hlo, hhi⟩ := ih init c0
    refine ⟨?_, ?_, ?_, ?_⟩
    · show _ / _ = _; rw [h1, pow_succ, Nat.div_div_eq_div_mul]
    · show (Array.push _ _).size = _; rw [Array.size_push, hsz]; omega
    · intro j hj
      rw [getElem!_push_lt _ _ _ (by rw [hsz]; omega), hlo j hj]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · rw [getElem!_push_lt _ _ _ (by rw [hsz]; omega), hhi j h]
      · subst h
        rw [show init.size + j
              = (List.foldl (fun (st : MProd Nat (Array β)) (_ : Nat) =>
                    ⟨st.1 / D, st.2.push (f (st.1 % D))⟩) ⟨c0, init⟩ (List.range' 0 j 1)).2.size
            from by rw [hsz], getElem!_push_eq, h1]

/-- Generic indexed-`set!` fold spec (do-notation `MProd ⟨cur, out⟩` state): `out.set! i (g (cur % D))`,
`cur /= D`, where the loop element `i` IS the write index. The `set!`-loop shape of `byteDecodeAt`'s unpacker
(vs `divPushFold_spec`'s `push`-loop shape). -/
theorem setFold_spec {β} [Inhabited β] (g : Nat → β) (D : Nat) :
    ∀ (n : Nat) (P0 : Array β) (c0 : Nat),
      let r := List.foldl (fun (st : MProd Nat (Array β)) (i : Nat) =>
                 ⟨st.1 / D, st.2.set! i (g (st.1 % D))⟩) ⟨c0, P0⟩ (List.range' 0 n 1)
      r.1 = c0 / D ^ n ∧ r.2.size = P0.size ∧
        (∀ j, j < n → j < P0.size → r.2[j]! = g (c0 / D ^ j % D)) ∧
        (∀ j, n ≤ j → r.2[j]! = P0[j]!) := by
  intro n
  induction n with
  | zero => intro P0 c0; simp
  | succ k ih =>
    intro P0 c0
    rw [List.range'_1_concat, List.foldl_concat]
    obtain ⟨h1, hsz, hlo, hhi⟩ := ih P0 c0
    refine ⟨?_, ?_, ?_, ?_⟩
    · show _ / _ = _; rw [h1, pow_succ, Nat.div_div_eq_div_mul]
    · show (Array.set! _ _ _).size = _
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz]
    · intro j hj hjsz
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · rw [getElem!_set!_ne _ _ _ _ (by omega), hlo j h hjsz]
      · subst h
        rw [Nat.zero_add, getElem!_set!_self _ _ _ (by rw [hsz]; exact hjsz), h1]
    · intro j hj
      rw [getElem!_set!_ne _ _ _ _ (by omega), hhi j (by omega)]

/-! ### The v4.35 `do`-notation state shapes

Lean v4.35 threads a `for` loop's mutable variables as a `Prod` in declaration order (it was an `MProd`
in reverse order). These bridges move each fold back to the `MProd` form the specs above are stated over. -/

theorem accFold_prod (g : Nat → Nat) (D n A m : Nat) :
    List.foldl (fun (st : Nat × Nat) (a : Nat) => (st.1 + g a * st.2, st.2 * D))
        (A, m) (List.range' 0 n 1)
      = (A + m * ∑ i ∈ Finset.range n, g i * D ^ i, m * D ^ n) := by
  have h := List.foldl_hom (fun s : MProd Nat Nat => ((s.1, s.2) : Nat × Nat))
    (g₁ := fun (st : MProd Nat Nat) (a : Nat) => (⟨st.1 + g a * st.2, st.2 * D⟩ : MProd Nat Nat))
    (g₂ := fun (st : Nat × Nat) (a : Nat) => (st.1 + g a * st.2, st.2 * D))
    (l := List.range' 0 n 1) (init := ⟨A, m⟩) (fun _ _ => rfl)
  rw [accFold] at h
  exact h

theorem divPushFold_prod {β} (f : Nat → β) (D n : Nat) (init : Array β) (c0 : Nat) :
    List.foldl (fun (st : Array β × Nat) (_ : Nat) => (st.1.push (f (st.2 % D)), st.2 / D))
        (init, c0) (List.range' 0 n 1)
      = ((List.foldl (fun (st : MProd Nat (Array β)) (_ : Nat) =>
            ⟨st.1 / D, st.2.push (f (st.1 % D))⟩) ⟨c0, init⟩ (List.range' 0 n 1)).2,
         (List.foldl (fun (st : MProd Nat (Array β)) (_ : Nat) =>
            ⟨st.1 / D, st.2.push (f (st.1 % D))⟩) ⟨c0, init⟩ (List.range' 0 n 1)).1) :=
  List.foldl_hom (fun s : MProd Nat (Array β) => ((s.2, s.1) : Array β × Nat))
    (init := ⟨c0, init⟩) (fun _ _ => rfl)

theorem setFold_prod {β} (g : Nat → β) (D n : Nat) (P0 : Array β) (c0 : Nat) :
    List.foldl (fun (st : Array β × Nat) (i : Nat) => (st.1.set! i (g (st.2 % D)), st.2 / D))
        (P0, c0) (List.range' 0 n 1)
      = ((List.foldl (fun (st : MProd Nat (Array β)) (i : Nat) =>
            ⟨st.1 / D, st.2.set! i (g (st.1 % D))⟩) ⟨c0, P0⟩ (List.range' 0 n 1)).2,
         (List.foldl (fun (st : MProd Nat (Array β)) (i : Nat) =>
            ⟨st.1 / D, st.2.set! i (g (st.1 % D))⟩) ⟨c0, P0⟩ (List.range' 0 n 1)).1) :=
  List.foldl_hom (fun s : MProd Nat (Array β) => ((s.2, s.1) : Array β × Nat))
    (init := ⟨c0, P0⟩) (fun _ _ => rfl)

/-- **Digit reconstruction**: the base-`b` digits of `N` up to position `n` reassemble `N % bⁿ`. -/
theorem digit_reconstruct (b : Nat) : ∀ (n N : Nat),
    ∑ m ∈ Finset.range n, (N / b ^ m % b) * b ^ m = N % b ^ n := by
  intro n
  induction n with
  | zero => intro N; simp [Nat.mod_one]
  | succ k ih =>
    intro N
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]
    ring

/-- **Digit bound**: a mixed-radix number with base-`b` digits is `< bⁿ`. -/
theorem digit_bound (b : Nat) (d : Nat → Nat) (hd : ∀ i, d i < b) :
    ∀ (n : Nat), (∑ i ∈ Finset.range n, d i * b ^ i) < b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have key : d k * b ^ k ≤ (b - 1) * b ^ k := by have := hd k; gcongr; omega
    have expand : (b - 1) * b ^ k + b ^ k = b ^ k * b := by
      have hb1 : b - 1 + 1 = b := by have := hd k; omega
      calc (b - 1) * b ^ k + b ^ k = (b - 1 + 1) * b ^ k := by ring
        _ = b * b ^ k := by rw [hb1]
        _ = b ^ k * b := by ring
    omega

theorem sum_peel (b : Nat) (e : Nat → Nat) (m : Nat) :
    (∑ i ∈ Finset.range (m + 1), e i * b ^ i)
      = e 0 + b * ∑ i ∈ Finset.range m, e (i + 1) * b ^ i := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one]
  rw [Nat.add_comm]
  exact congrArg (e 0 + ·) (Finset.sum_congr rfl (fun i _ => by ring))

theorem sum_div_one (b : Nat) (hb : 0 < b) (e : Nat → Nat) (he0 : e 0 < b) :
    ∀ M, (∑ i ∈ Finset.range M, e i * b ^ i) / b = ∑ i ∈ Finset.range (M - 1), e (i + 1) * b ^ i := by
  intro M
  cases M with
  | zero => simp
  | succ m =>
    rw [sum_peel b e m, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt he0, Nat.zero_add,
      Nat.add_sub_cancel]

theorem sum_div_pow (b : Nat) (hb : 0 < b) (d : Nat → Nat) (hd : ∀ i, d i < b) :
    ∀ (j n : Nat),
      (∑ i ∈ Finset.range n, d i * b ^ i) / b ^ j = ∑ i ∈ Finset.range (n - j), d (i + j) * b ^ i := by
  intro j
  induction j with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ih n,
      sum_div_one b hb (fun i => d (i + k)) (by simpa using hd k)]
    refine Finset.sum_congr (by rw [Nat.sub_sub]) (fun i _ => ?_)
    simp only [show i + 1 + k = i + (k + 1) from by omega]

theorem sum_mod_base (b : Nat) (e : Nat → Nat) (he0 : e 0 < b) :
    ∀ M, 0 < M → (∑ i ∈ Finset.range M, e i * b ^ i) % b = e 0 := by
  intro M hM
  cases M with
  | zero => omega
  | succ m =>
    rw [sum_peel b e m, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he0]

/-- **Digit extraction**: the `j`-th base-`b` digit of `∑ dᵢ bⁱ` is `d j` (digits `< b`, `j < n`). -/
theorem extract_digit (b : Nat) (hb : 0 < b) (d : Nat → Nat) (hd : ∀ i, d i < b)
    (n j : Nat) (hj : j < n) :
    (∑ i ∈ Finset.range n, d i * b ^ i) / b ^ j % b = d j := by
  rw [sum_div_pow b hb d hd j n]
  have := sum_mod_base b (fun i => d (i + j)) (by simpa using hd j) (n - j) (by omega)
  simpa using this

theorem arrayExtAll {β} [Inhabited β] (a c : Array β) (hs : a.size = c.size)
    (h : ∀ i, i < a.size → getElem! a i = getElem! c i) : a = c := by
  apply Array.ext hs
  intro i h1 h2
  have hh := h i h1
  rwa [getElem!_pos a i h1, getElem!_pos c i h2] at hh

/-! ## The ML-KEM `byteEncode` big-`Nat`, and its emitted bytes. -/

/-- The little-endian mixed-radix integer packed by `byteEncode`'s accumulate loop
(`∑_{i<256} (fᵢ mod 2ᵈ)·(2ᵈ)ⁱ`). -/
def packNatKem (f : Poly) (d : Nat) : Nat :=
  ∑ i ∈ Finset.range 256, (f[i]! % 2 ^ d) * (2 ^ d) ^ i

/-- **`byteEncode` as an explicit emit array.** `(byteEncode d f).toArray` is the base-`256` little-endian
emit of `packNatKem f d` into `polyBytes d` bytes. -/
theorem byteEncode_toArray (d : Nat) (f : Poly) :
    (byteEncode d f).toArray =
      (List.foldl (fun (st : MProd Nat (Array UInt8)) (_ : Nat) =>
          ⟨st.1 / 256, st.2.push (UInt8.ofNat (st.1 % 256))⟩)
        ⟨packNatKem f d, Array.mkEmpty (polyBytes d)⟩ (List.range' 0 (polyBytes d) 1)).2 := by
  unfold byteEncode
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rw [accFold_prod (fun i => f[i]! % 2 ^ d) (2 ^ d) 256 0 1,
    show (0 + 1 * ∑ i ∈ Finset.range 256, f[i]! % 2 ^ d * (2 ^ d) ^ i) = packNatKem f d from by
      rw [Nat.zero_add, Nat.one_mul]; rfl,
    divPushFold_prod UInt8.ofNat 256 (polyBytes d)]
  rfl

theorem byteEncode_size (d : Nat) (f : Poly) : (byteEncode d f).toArray.size = polyBytes d := by
  rw [byteEncode_toArray]
  have hspec := divPushFold_spec UInt8.ofNat 256 (polyBytes d)
    (Array.mkEmpty (polyBytes d)) (packNatKem f d)
  have hsz := hspec.2.1
  rw [size_mkEmpty, Nat.zero_add] at hsz
  exact hsz

theorem byteEncode_getElem (d : Nat) (f : Poly) (m : Nat) (hm : m < polyBytes d) :
    (byteEncode d f).toArray[m]! = UInt8.ofNat (packNatKem f d / 256 ^ m % 256) := by
  rw [byteEncode_toArray]
  have hspec := divPushFold_spec UInt8.ofNat 256 (polyBytes d)
    (Array.mkEmpty (polyBytes d)) (packNatKem f d)
  have hkey := hspec.2.2.2 m hm
  rw [size_mkEmpty, Nat.zero_add] at hkey
  exact hkey

/-- `bytesToNatLE` as an explicit positional sum. -/
theorem bytesToNatLE_eq (b : Array UInt8) (off len : Nat) :
    bytesToNatLE b off len = ∑ i ∈ Finset.range len, (b[off + i]!).toNat * 256 ^ i := by
  unfold bytesToNatLE
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp,
    map_pure, List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_one_sub_one, Nat.div_one]
  rw [accFold_prod (fun i => (b[off + i]!).toNat) 256 len 0 1]
  simp only [Nat.zero_add, Nat.one_mul]; rfl

/-- **`packNatKem` is `< 256^{polyBytes d}`** — its digits are `< 2ᵈ` and `polyBytes d = 32·d`, so it fits in
the emitted byte count (`(2ᵈ)²⁵⁶ = 256^{32·d}`). -/
theorem packNatKem_lt (d : Nat) (f : Poly) : packNatKem f d < 256 ^ polyBytes d := by
  have hpos : (0 : Nat) < 2 ^ d := by positivity
  have hbase : (2 ^ d) ^ 256 = 256 ^ polyBytes d := by
    show (2 ^ d) ^ 256 = 256 ^ (32 * d)
    rw [show (256 : Nat) = 2 ^ 8 from by norm_num, ← pow_mul, ← pow_mul]
    congr 1; ring
  rw [← hbase]
  exact digit_bound (2 ^ d) (fun i => f[i]! % 2 ^ d) (fun i => Nat.mod_lt _ hpos) 256

/-- **Byte round-trip**: reading back the bytes `byteEncode` emitted reconstructs `packNatKem` exactly. -/
theorem bytesToNatLE_byteEncode (d : Nat) (f : Poly) :
    bytesToNatLE (byteEncode d f).toArray 0 (polyBytes d) = packNatKem f d := by
  rw [bytesToNatLE_eq, ← Nat.mod_eq_of_lt (packNatKem_lt d f),
    ← digit_reconstruct 256 (polyBytes d) (packNatKem f d)]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm' : m < polyBytes d := Finset.mem_range.mp hm
  rw [Nat.zero_add, byteEncode_getElem d f m hm', UInt8.toNat_ofNat',
    Nat.mod_mod_of_dvd _ (dvd_refl 256)]

/-! ## THE CODEC ROUND-TRIP — `byteDecodeAt d (byteEncode d f).toArray 0 = f`, ∀. -/

/-- The effective decode modulus: `q` for the `d = 12` `ByteDecode₁₂` (which reduces mod `q`), else `2ᵈ`. -/
def decMod (d : Nat) : Nat := if d == 12 then q else 2 ^ d

/-- `byteDecodeAt` always produces a size-256 poly (the unpack loop `set!`s into `zeroPoly`). -/
theorem byteDecodeAt_size (d : Nat) (b : Array UInt8) (off : Nat) :
    (byteDecodeAt d b off).size = 256 := by
  unfold byteDecodeAt
  simp only [Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rw [setFold_prod (β := Nat) (fun v => if d == 12 then v % q else v) (2 ^ d) 256 zeroPoly]
  have hspec := setFold_spec (β := Nat) (fun v => if d == 12 then v % q else v) (2 ^ d) 256 zeroPoly
    (bytesToNatLE b off (polyBytes d))
  have hsz := hspec.2.1
  rw [show zeroPoly.size = 256 from by simp [zeroPoly]] at hsz
  -- reduce the `Prod.fst` of the pair syntactically (`exact` would whnf the 256-step fold instead)
  dsimp only
  exact hsz

/-- **`byteDecodeAt`'s `j`-th coefficient** is the base-`2ᵈ` digit `j` of `bytesToNatLE`, reduced mod `q` when
`d = 12` (the `ByteDecode₁₂` codomain). -/
theorem byteDecodeAt_getElem (d : Nat) (b : Array UInt8) (off j : Nat) (hj : j < 256) :
    (byteDecodeAt d b off)[j]!
      = (if d == 12 then bytesToNatLE b off (polyBytes d) / (2 ^ d) ^ j % 2 ^ d % q
         else bytesToNatLE b off (polyBytes d) / (2 ^ d) ^ j % 2 ^ d) := by
  unfold byteDecodeAt
  simp only [Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rw [setFold_prod (β := Nat) (fun v => if d == 12 then v % q else v) (2 ^ d) 256 zeroPoly]
  have hspec := setFold_spec (β := Nat) (fun v => if d == 12 then v % q else v) (2 ^ d) 256 zeroPoly
    (bytesToNatLE b off (polyBytes d))
  have hkey := hspec.2.2.1 j hj (by rw [show zeroPoly.size = 256 from by simp [zeroPoly]]; exact hj)
  dsimp only
  exact hkey

/-- **THE ML-KEM CODEC ROUND-TRIP** (the `byteDecode ∘ byteEncode = id` the `DecapsCoreSpec` /
`EncapsCoreSpec` residuals named). For a size-256 coefficient array whose entries are all below the codec's
effective modulus (`2ᵈ` for the compressed widths `d < 12`, `q` for the `d = 12` NTT-domain widths — the
`ByteDecode₁₂` codomain), encoding then decoding is the identity. Pure positional-`Nat` arithmetic through the
`Id.run do` accumulate/emit + read/`set!` loops — no `native_decide`, no hardness. -/
theorem byteDecodeAt_byteEncode (d : Nat) (f : Poly)
    (hsz : f.size = 256) (hlt : ∀ j, j < 256 → f[j]! < decMod d) :
    byteDecodeAt d (byteEncode d f).toArray 0 = f := by
  have hpos : (0 : Nat) < 2 ^ d := by positivity
  -- `decMod d ≤ 2 ^ d` in both branches (q = 3329 < 4096 = 2^12; else equality).
  have hmod_le : decMod d ≤ 2 ^ d := by
    unfold decMod
    split
    · rename_i h; rw [beq_iff_eq] at h; subst h; unfold q; norm_num
    · exact le_refl _
  -- each coefficient equals its own `mod 2^d` (they are below `decMod ≤ 2^d`).
  have hfmod : ∀ j, j < 256 → f[j]! % 2 ^ d = f[j]! :=
    fun j hj => Nat.mod_eq_of_lt (lt_of_lt_of_le (hlt j hj) hmod_le)
  refine arrayExtAll _ _ ?_ ?_
  · rw [byteDecodeAt_size, hsz]
  · intro j hj
    rw [byteDecodeAt_size] at hj
    rw [byteDecodeAt_getElem d _ 0 j hj, bytesToNatLE_byteEncode d f]
    -- the `j`-th base-`2^d` digit of `packNatKem` is `f[j]! mod 2^d = f[j]!`.
    have hdigit : packNatKem f d / (2 ^ d) ^ j % 2 ^ d = f[j]! := by
      unfold packNatKem
      rw [extract_digit (2 ^ d) hpos (fun i => f[i]! % 2 ^ d) (fun i => Nat.mod_lt _ hpos) 256 j hj]
      exact hfmod j hj
    rw [hdigit]
    -- discharge the `if d == 12` reduction: `f[j]! < q` in that branch, else nothing to reduce.
    by_cases h12 : d = 12
    · subst h12
      simp only [beq_self_eq_true, if_true]
      exact Nat.mod_eq_of_lt (by simpa [decMod] using hlt j hj)
    · simp only [beq_iff_eq, if_neg h12]

#assert_axioms byteDecodeAt_byteEncode

/-! ## Instantiation at the four ML-KEM codec widths. -/

/-- **`d = 12` — the `t̂`/`ŝ` NTT-domain codec.** Any size-256 poly with coeffs `< q` round-trips
`ByteEncode₁₂ / ByteDecode₁₂`. -/
theorem byteDecode₁₂_byteEncode₁₂ (f : Poly) (hsz : f.size = 256) (hlt : ∀ j, j < 256 → f[j]! < q) :
    byteDecode dCoeff (byteEncode dCoeff f) = f := by
  unfold byteDecode
  exact byteDecodeAt_byteEncode dCoeff f hsz (by simpa [decMod, dCoeff] using hlt)

/-- **`du = 10` — the ciphertext `u` codec.** Any size-256 poly with coeffs `< 2¹⁰` round-trips. -/
theorem byteDecode_du_byteEncode_du (f : Poly) (hsz : f.size = 256)
    (hlt : ∀ j, j < 256 → f[j]! < 2 ^ du) :
    byteDecode du (byteEncode du f) = f := by
  unfold byteDecode
  exact byteDecodeAt_byteEncode du f hsz (by simpa [decMod, du] using hlt)

/-- **`dv = 4` — the ciphertext `v` codec.** Any size-256 poly with coeffs `< 2⁴` round-trips. -/
theorem byteDecode_dv_byteEncode_dv (f : Poly) (hsz : f.size = 256)
    (hlt : ∀ j, j < 256 → f[j]! < 2 ^ dv) :
    byteDecode dv (byteEncode dv f) = f := by
  unfold byteDecode
  exact byteDecodeAt_byteEncode dv f hsz (by simpa [decMod, dv] using hlt)

/-- **`d = 1` — the message codec.** Any size-256 `{0,1}`-poly round-trips `ByteEncode₁ / ByteDecode₁`. -/
theorem byteDecode₁_byteEncode₁ (f : Poly) (hsz : f.size = 256) (hlt : ∀ j, j < 256 → f[j]! < 2) :
    byteDecode 1 (byteEncode 1 f) = f := by
  unfold byteDecode
  exact byteDecodeAt_byteEncode 1 f hsz (by simpa [decMod] using hlt)

#assert_axioms byteDecode₁₂_byteEncode₁₂
#assert_axioms byteDecode_du_byteEncode_du
#assert_axioms byteDecode_dv_byteEncode_dv
#assert_axioms byteDecode₁_byteEncode₁

/-! ## NON-VACUITY — the round-trip fires on a genuine, non-degenerate NTT-domain poly.

The `d = 12` hypothesis (coeffs `< q`) is satisfiable and the identity is not vacuous: `zeroPoly` has size 256
and all coeffs `0 < q`, and a nonzero coefficient survives the round-trip too. We witness on a poly with a
`3328 = q − 1` coefficient (the top `< q` value), which encodes to two nonzero low bytes and decodes back. -/

/-- A witness NTT-domain poly: `zeroPoly` with slot 0 set to `q − 1 = 3328` (the maximal `< q` coefficient). -/
def witPoly : Poly := zeroPoly.set! 0 (q - 1)

theorem witPoly_size : witPoly.size = 256 := by unfold witPoly; simp [zeroPoly]

theorem witPoly_lt : ∀ j, j < 256 → witPoly[j]! < q := by
  intro j hj
  unfold witPoly
  by_cases h : j = 0
  · subst h; rw [getElem!_set!_self _ _ _ (by simp [zeroPoly])]; unfold q; omega
  · rw [getElem!_set!_ne _ _ _ _ (by omega), zeroPoly_get j hj]; unfold q; omega

/-- **Non-vacuity**: the `d = 12` codec round-trip FIRES on a genuine poly carrying the maximal `< q`
coefficient (`q − 1`), not just the all-zero poly — `byteDecode₁₂ ∘ byteEncode₁₂` recovers it exactly. -/
theorem byteDecode₁₂_byteEncode₁₂_witness :
    byteDecode dCoeff (byteEncode dCoeff witPoly) = witPoly :=
  byteDecode₁₂_byteEncode₁₂ witPoly witPoly_size witPoly_lt

/-- Non-vacuity teeth: `witPoly` genuinely differs from `zeroPoly` (its slot 0 is `q − 1 ≠ 0`), so the
round-trip is not the trivial `zeroPoly` case. -/
theorem witPoly_ne_zero : witPoly ≠ zeroPoly := by
  intro h
  have h0 : witPoly[0]! = q - 1 := by
    unfold witPoly; exact getElem!_set!_self _ _ _ (by simp [zeroPoly])
  rw [h, zeroPoly_get 0 (by omega)] at h0
  unfold q at h0; omega

end Dregg2.Crypto.MlKemCodecSpec
