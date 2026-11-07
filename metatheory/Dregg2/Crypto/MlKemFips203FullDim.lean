/-
# `Dregg2.Crypto.MlKemFips203FullDim` — `Fips203Correct` at REAL ML-KEM-768 DIMENSION.

`DreggKemRefinement.dregg_kem_correct` — the deployed `dregg-pq` hybrid-handshake agreement theorem — takes
`hfips : Fips203Correct api` as its ML-KEM floor. That floor WAS discharged, but only at
`Fips203Kem.extractedKemApi`: a `k = 1`, `n = 1`, `A = 1`, `s = e = 1`, message-`m = 1` SCALAR caricature over
`ℤ` — not the `n = 256` negacyclic ring, not ML-KEM-768. This module discharges the SAME `Fips203Correct`
(the definition is NOT weakened) at the REAL parameters: `k = 3`, `η₁ = η₂ = 2`, `d_u = 10`, `d_v = 4`,
`n = 256`, `q = 3329`, over the byte-exact executable ML-KEM-768 of `MlKemDecaps`/`MlKemEncaps` — 1184-byte
`ek`, 2400-byte `dk`, 1088-byte `ct`, 32-byte `K`, SHA3-512 `G` / SHA3-256 `H` / SHAKE-256 `J`, the incomplete
Kyber NTT, the CBD sampler, and both compression codecs.

## The three theorems, and what each one costs

1. **`mlkem_roundtrip_of_kpke` — the FO/KEM layer, PROVED.** For any well-formed decapsulation key
   (`wfDk`: the embedded `h` really is `H(ek)`), `ML-KEM.Decaps(dk, ML-KEM.Encaps(ek, m))` returns EXACTLY the
   encapsulated `K`, given ONE event: K-PKE decryption recovers `m`. The Fujisaki–Okamoto machinery —
   `(K,r) = G(m ‖ H(ek))`, the re-encryption `c' = K-PKE.Encrypt(ek, m', r')`, the byte-exact `c' = c` gate,
   the implicit-reject branch — is DISCHARGED, not assumed: once `m' = m` the two `G` calls coincide, so
   `r' = r`, so `c'` is the SAME `kpkeEncrypt` call as `c`, the gate fires, and `K' = K`. This is the whole
   security-critical FO layer at full dimension, kernel-clean.

2. **`kpkeDecrypt_recovers` — K-PKE decryption, PROVED from the FIPS 203 noise window.** `kpkeDecrypt`
   computes `w = v − NTT⁻¹(ŝᵀ ∘ NTT(u))` and returns `ByteEncode₁(Compress₁(w))`. Define the decryption noise
   `e_c := centered(w_c − m_c·1665) ∈ (−q/2, q/2]` — the ACTUAL noise of the ACTUAL executable pipeline, at
   this key / message / coins. If every `|e_c| < 832 = ⌊q/4⌋` (`noiseWindow`, the FIPS 203 decision window),
   then `Compress₁(w) = ByteDecode₁(m)` (`MlKemCorrect.compress1_recover_zmod`, coefficient by coefficient,
   over the real `ℤ_q`), and `ByteEncode₁ ∘ ByteDecode₁ = id` on any 32-byte message
   (`byteEncode₁_byteDecode₁`, the positional-numeral inverse, proved here — the mirror of
   `MlKemCodecSpec.byteDecodeAt_byteEncode`). So `kpkeDecrypt dkPke (kpkeEncrypt ek m r) = m`. No
   `native_decide`; the symbolic route throughout.

3. **`fullKemApi_fips203` — `Fips203Correct` at ML-KEM-768.** The API's decapsulation-key type is the
   SUBTYPE of byte keys that are well-formed AND in-window (`goodKey`). That is not a dodge: FIPS 203
   correctness IS `δ`-correctness — ML-KEM decryption genuinely FAILS on the (astronomically rare) keys whose
   noise escapes the window, so a `∀ dk : List UInt8` statement would be FALSE. Conditioning on exactly the
   event whose probability `MlKemDelta` bounds is the honest full-dimension statement.

## Wired to `MlKemDelta`'s `δ`

`MlKemDelta` proves — unconditionally, in-kernel — that the modeled ML-KEM-768 `e_total` ENVELOPE
`MlKemDelta.mlkemZ` escapes the `(−832, 832)` window at some coefficient with probability `≤ δ`
(`mlkem768_decapsFailure_le_delta_unconditional`: `δ = 2⁻¹⁴⁰`; the tightened
`…_unconditional_tight`, where the tree carries it: `δ = 2⁻¹⁴⁸`). That analytic bound is NOT re-proved here —
it enters this module as the NAMED, THREADED obligation `EnvelopeDeltaBound δ` (§6). `roundtrip_fails_le_delta`
transports it by STOCHASTIC DOMINATION: for any key sampler whose true decaps-failure event is CONTAINED in the
envelope's failure event (the NAMED domination `hdom`, below), the full-dimension encaps→decaps round trip
fails with probability `≤ δ`. `roundtrip_fails_le_delta_2pow140` is the unconditional `δ = 2⁻¹⁴⁰` instance.
That is `Fips203Correct`-except-`δ` at real ML-KEM-768 parameters.

## ⚑ THE ONE NAMED RESIDUAL — `hdom` (the envelope's stochastic DOMINATION of the true noise)

**Why domination, not equality.** `MlKemDelta.mlkemZ` is NOT the literal executable noise: it is a
conservative MGF-*envelope* surrogate — its `Δv` term is the `±104` EXTREME point `MlKemDelta.dvX` (not the
literal rounding `Δv ∈ [−104,104]`), and its cross-terms `eᵀr, sᵀe1, sᵀΔu` are the `cbd²`-PRODUCT envelopes
(`MlKemDelta.mlkemZ`'s header calls the step to the literal randomness an "MGF-DOMINATION step", §13). So the
executable pipeline's noise `centered(w_c − m_c·1665)` does NOT *equal* `mlkemZ` coefficient-by-coefficient
(the envelope over-bounds it) — an earlier draft asserted that equality as a hypothesis `hbridge`, which is
FALSE, hence made the theorem vacuous. What genuinely holds is DOMINATION at the event level: the envelope's
`Δv = ±104` and `cbd²` extreme points upper-bound the true per-term contributions, so whenever the TRUE noise
escapes the decode window at some coefficient (⇒ decaps failure), the ENVELOPE model `mlkemZ` also registers a
failure. Equivalently: `{envelope registers no failure} ⊆ {true noise in-window everywhere}`. That is exactly
`hdom`, and it is what the envelope was BUILT to support.

`hdom` is a HYPOTHESIS of `roundtrip_fails_le_delta` (never a `def …Hard` carrier, never an axiom, and
`#assert_axioms` is blind to it — so it is stated here in the open). It is SATISFIABLE, not vacuous:
`roundtrip_fails_le_delta_nonvacuous` (§7) discharges it for the constant sampler at the genuine `ml-kem`
crate key, where the true noise is in-window everywhere (so `hdom` holds and δ transports).

**Fully DISCHARGING `hdom` (rather than hypothesizing it)** is the remaining MGF-domination lane: it needs the
byte-level algebraic cancellation `MlKemCorrect.mlkem_decrypt_cancellation` (PROVED, over abstract `[CommRing
R]`, hence over the real `R_q`) INSTANTIATED at the executable `Array Nat` pipeline to exhibit the true noise
as `MlKemCorrect.eTotal`, then the §13 byte-faithful grouped MGF-domination (`MlKemDelta.bf*`) applied to that
literal noise. `MlKemNttFaithful` supplies the NTT leg (`ntt_computes_negacyclic_mul` / `ntt_intt_id` as
∀-theorems, so the NTT fast path IS the negacyclic product); §8 below (`intt_addLinear`, `ntt_intt_rightInverse`)
adds the reusable `intt`-linearity + `ntt∘intt = id` legs; the remaining named pieces are the `Poly → R_q`
coefficient ring hom on the matrix–vector K-PKE algebra and the byte-codec / ExpandA / CBD sampler
faithfulness (each named precisely in §8).

The unconditional facts here — 1, 2, 3 — do NOT use `hdom`. `fullKemApi_fips203` is a genuine
`Fips203Correct` at ML-KEM-768, kernel-clean.

## NON-VACUITY (the only `native_decide`s in this file, ISOLATED to concrete byte checks in §7)

`realDk_good` checks — on the GENUINE `ml-kem` v0.2.3 crate key `MlKemCodec.realDk` and the pinned message
`MlKemEncaps.acvpM` — that `goodKey` holds: the key is well-formed AND every one of the 256 decryption-noise
coefficients is inside the window. It is a concrete KAT-shaped `Bool` evaluation over 2400+1088 real bytes, so
it (with `ekOfDk_realDk` and the refutable tooth `zeroDk_not_good`) goes by `native_decide`
(`Lean.ofReduceBool` + `Lean.trustCompiler`, the residual `MlKemCodec` / `MlKemDecaps` / `Keccak` already
name). It inhabits the subtype — so `fullKemApi_fips203` is NOT vacuous — and NONE of these appear in any
∀-theorem's axiom set (the `#assert_all_clean` list below excludes them).
-/
import Dregg2.Crypto.MlKemEncaps
import Dregg2.Crypto.MlKemCodecSpec
import Dregg2.Crypto.MlKemNttFaithful
import Dregg2.Crypto.MlKemCorrect
import Dregg2.Crypto.MlKemDelta
import Dregg2.Crypto.DecapsCoreSpec
import Dregg2.Crypto.DreggKemRefinement

namespace Dregg2.Crypto.MlKemFips203FullDim

open Dregg2.Crypto
open Dregg2.Crypto.MlKemRing (Poly q zeroPoly ntt intt pointwiseNtt addPoly subPoly subQ mulModQ)
open Dregg2.Crypto.MlKemCodec
open Dregg2.Crypto.MlKemCodecSpec
open Dregg2.Crypto.MlKemDecaps (kpkeDecrypt kpkeEncrypt mlkemDecaps sha3_256 sha3_512)
open Dregg2.Crypto.MlKemEncaps (mlkemEncaps)
open Dregg2.Crypto.DreggKemRefinement
open Dregg2.Crypto.ProbCrypto (winProb)

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! ## §1 — `ByteEncode₁ ∘ ByteDecode₁ = id` on a 32-byte message (the codec direction `MlKemCodecSpec` did
not need). Pure positional-numeral arithmetic over the codec's own big-`Nat` (un)packer — no `native_decide`. -/

/-- The 256-bit message polynomial `ByteDecode₁(m)` — coefficient `i` is bit `i` of the 32-byte `m`. -/
def msgPoly (m : List UInt8) : Poly := byteDecode 1 m

theorem msgPoly_size (m : List UInt8) : (msgPoly m).size = 256 := byteDecodeAt_size 1 _ 0

/-- Every message-poly coefficient is a BIT (`< 2`) — the `ByteDecode₁` codomain. -/
theorem msgPoly_lt2 (m : List UInt8) (j : Nat) (hj : j < 256) : (msgPoly m)[j]! < 2 := by
  unfold msgPoly byteDecode
  rw [byteDecodeAt_getElem 1 _ 0 j hj, if_neg (by decide : ¬ (((1 : Nat) == 12) = true))]
  exact Nat.mod_lt _ (by norm_num)

/-- `256³² = 2²⁵⁶`, proved WITHOUT the kernel ever forming the astronomical `2²⁵⁶` numeral (base folded to
`2⁸` by `congr`, exponents combined by `pow_mul`, `8·32 = 256` by defeq). -/
theorem pow_256_32 : (256 : Nat) ^ 32 = 2 ^ 256 := by
  have h1 : (256 : Nat) ^ 32 = (2 ^ 8) ^ 32 := by congr 1
  have h2 : ((2 : Nat) ^ 8) ^ 32 = 2 ^ (8 * 32) := (pow_mul 2 8 32).symm
  have h3 : (8 * 32 : Nat) = 256 := by norm_num
  rw [h1, h2, h3]

/-- The little-endian value of a 32-byte message is `< 2²⁵⁶` (32 base-`256` digits). -/
theorem bytesToNatLE_lt (m : List UInt8) (_hm : m.length = 32) :
    bytesToNatLE m.toArray 0 32 < 2 ^ 256 := by
  rw [bytesToNatLE_eq]
  have hb := digit_bound 256 (fun i => (m.toArray[0 + i]!).toNat)
    (fun i => (m.toArray[0 + i]!).toNat_lt_size) 32
  rw [← pow_256_32]
  exact hb

/-- **The message codec's OTHER direction**: re-encoding the decoded bits of any 32-byte message gives the
message back — `ByteEncode₁(ByteDecode₁(m)) = m`. (`MlKemCodecSpec.byteDecode₁_byteEncode₁` is the mirror:
decode-after-encode. This is encode-after-decode, which the decryption round trip needs.) -/
theorem byteEncode₁_byteDecode₁ (m : List UInt8) (hm : m.length = 32) :
    byteEncode 1 (msgPoly m) = m := by
  set N := bytesToNatLE m.toArray 0 32 with hN
  have hsizeM : m.toArray.size = 32 := by simp [hm]
  -- the decoded coefficients are the base-2 digits of `N`.
  have hcoeff : ∀ j, j < 256 → (msgPoly m)[j]! = N / 2 ^ j % 2 := by
    intro j hj
    unfold msgPoly byteDecode
    rw [byteDecodeAt_getElem 1 _ 0 j hj, if_neg (by decide : ¬ (((1 : Nat) == 12) = true))]
    simp only [pow_one]
    rfl
  -- hence `packNatKem` reassembles `N` exactly (`N < 2^256`).
  have hpack : packNatKem (msgPoly m) 1 = N := by
    unfold packNatKem
    have hcong : ∀ i ∈ Finset.range 256,
        ((msgPoly m)[i]! % 2 ^ 1) * (2 ^ 1) ^ i = (N / 2 ^ i % 2) * 2 ^ i := by
      intro i hi
      rw [hcoeff i (Finset.mem_range.mp hi), pow_one,
        Nat.mod_mod_of_dvd _ (dvd_refl 2)]
    rw [Finset.sum_congr rfl hcong, digit_reconstruct 2 256 N]
    exact Nat.mod_eq_of_lt (bytesToNatLE_lt m hm)
  -- the emitted bytes are the base-256 digits of `N`, i.e. `m` itself.
  have harr : (byteEncode 1 (msgPoly m)).toArray = m.toArray := by
    refine arrayExtAll _ _ ?_ ?_
    · rw [byteEncode_size]; simp [polyBytes, hsizeM]
    · intro j hj
      rw [byteEncode_size] at hj
      have hj32 : j < 32 := by simpa [polyBytes] using hj
      rw [byteEncode_getElem 1 _ j (by simpa [polyBytes] using hj32), hpack, hN, bytesToNatLE_eq]
      rw [extract_digit 256 (by norm_num) (fun i => (m.toArray[0 + i]!).toNat)
        (fun i => (m.toArray[0 + i]!).toNat_lt_size) 32 j hj32]
      simp
  have := congrArg Array.toList harr
  simpa using this

/-! ## §2 — the K-PKE decrypt `w`, and the FIPS 203 decryption-noise WINDOW at the executable pipeline. -/

/-- The `Σᵢ ŝᵢ ∘ NTT(uᵢ)` accumulator `K-PKE.Decrypt` builds (FIPS 203 Alg 14). -/
def kpkeAcc (dkPke : List UInt8) (c : List UInt8) : Poly := Id.run do
  let (u, _v) := ctDecode c
  let dkArr := dkPke.toArray
  let mut acc : Poly := zeroPoly
  for i in [0:paramK] do
    let sHat_i := byteDecodeAt dCoeff dkArr (i * polyBytes dCoeff)
    acc := addPoly acc (pointwiseNtt sHat_i (ntt u[i]!))
  return acc

/-- **The decrypted ring element** `w = v − NTT⁻¹(Σᵢ ŝᵢ ∘ NTT(uᵢ))` — the object `K-PKE.Decrypt` compresses
into the message. Factored out of `MlKemDecaps.kpkeDecrypt` verbatim. -/
def kpkeW (dkPke : List UInt8) (c : List UInt8) : Poly :=
  subPoly (ctDecode c).2 (intt (kpkeAcc dkPke c))

/-- `K-PKE.Decrypt` IS `ByteEncode₁ ∘ Compress₁ ∘ w` — definitional (the factoring is exact). -/
theorem kpkeDecrypt_eq (dkPke c : List UInt8) :
    kpkeDecrypt dkPke c = byteEncode 1 (compressPoly 1 (kpkeW dkPke c)) := rfl

theorem kpkeW_lt (dkPke c : List UInt8) (p : Nat) : (kpkeW dkPke c)[p]! < q :=
  MlKemRing.subPoly_lt _ _ p

theorem kpkeW_size (dkPke c : List UInt8) : (kpkeW dkPke c).size = 256 :=
  MlKemRing.subPoly_size _ _

/-- `(3329 : ZMod 3329) = 0` — the ML-KEM modulus vanishes in its own residue ring. -/
theorem c3329 : (3329 : ZMod 3329) = 0 := by simpa using ZMod.natCast_self 3329

/-- The centered lift of a canonical `ℤ_q` rep into `(−q/2, q/2]` — `x` for `x ≤ 1664`, `x − 3329` above. -/
def centeredQ (x : Nat) : ℤ := if x ≤ 1664 then (x : ℤ) else (x : ℤ) - 3329

theorem centeredQ_cast (x : Nat) : ((centeredQ x : ℤ) : ZMod 3329) = (x : ZMod 3329) := by
  unfold centeredQ
  split
  · push_cast; ring
  · push_cast; rw [c3329]; ring

/-- **THE DECRYPTION NOISE of the EXECUTABLE pipeline**, coefficient `i`: the centered lift of
`w_i − m_i·⌈q/2⌉` in `ℤ_q`. This is `e_total`'s `i`-th coefficient AS THE RUNNING CODE COMPUTES IT — not a
model of it. -/
def noiseAt (w mp : Poly) (i : Nat) : ℤ := centeredQ (subQ (w[i]!) (mulModQ (mp[i]!) 1665))

/-- **THE FIPS 203 DECRYPTION WINDOW** — every one of the 256 noise coefficients inside `(−832, 832)`
(`832 = ⌊q/4⌋`, the exact decision threshold; `MlKemCorrect.compress1_tight` shows `832` itself FLIPS a bit). -/
def noiseWindow (w mp : Poly) : Bool :=
  (List.range 256).all (fun i => decide (-832 < noiseAt w mp i ∧ noiseAt w mp i < 832))

theorem noiseWindow_at (w mp : Poly) (h : noiseWindow w mp = true) (i : Nat) (hi : i < 256) :
    -832 < noiseAt w mp i ∧ noiseAt w mp i < 832 := by
  unfold noiseWindow at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.mpr hi)
  simpa using this

/-! ### `ℤ_q` casts of the executable's `Nat` modular ops (into `ZMod 3329`, where the recovery lemma lives). -/

theorem cast_subQ' (a b : Nat) (h : b < 3329) :
    ((subQ a b : Nat) : ZMod 3329) = (a : ZMod 3329) - (b : ZMod 3329) :=
  MlKemRing.cast_subQ a b (by unfold MlKemRing.q; omega)

theorem cast_mulModQ' (a b : Nat) :
    ((mulModQ a b : Nat) : ZMod 3329) = (a : ZMod 3329) * (b : ZMod 3329) :=
  MlKemRing.cast_mulModQ a b

/-! ### `compressPoly`'s entrywise spec (the indexed-`set!` loop). -/

/-- Generic indexed-`set!` fold (the loop shape of `compressPoly`: the loop variable IS the write index). -/
theorem idxSetFold_spec {β : Type*} [Inhabited β] (g : Nat → β) :
    ∀ (n : Nat) (P0 : Array β),
      let r := List.foldl (fun (out : Array β) (i : Nat) => out.set! i (g i)) P0 (List.range' 0 n 1)
      r.size = P0.size ∧ (∀ j, j < n → j < P0.size → r[j]! = g j) := by
  intro n
  induction n with
  | zero => intro P0; simp
  | succ k ih =>
    intro P0
    rw [List.range'_1_concat, List.foldl_concat]
    obtain ⟨hsz, hlo⟩ := ih P0
    refine ⟨?_, ?_⟩
    · show (Array.set! _ _ _).size = _
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz]
    · intro j hj hjsz
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · rw [getElem!_set!_ne _ _ _ _ (by omega), hlo j h hjsz]
      · subst h
        rw [Nat.zero_add, getElem!_set!_self _ _ _ (by rw [hsz]; exact hjsz)]

theorem compressPoly_fold (d : Nat) (p : Poly) :
    compressPoly d p =
      List.foldl (fun (out : Poly) (i : Nat) => out.set! i (compress d p[i]!)) zeroPoly
        (List.range' 0 256 1) := by
  unfold compressPoly
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

theorem compressPoly_size (d : Nat) (p : Poly) : (compressPoly d p).size = 256 := by
  rw [compressPoly_fold]
  have h := idxSetFold_spec (fun i => compress d p[i]!) 256 zeroPoly
  rw [h.1]
  simp [zeroPoly]

theorem compressPoly_getElem (d : Nat) (p : Poly) (j : Nat) (hj : j < 256) :
    (compressPoly d p)[j]! = compress d p[j]! := by
  rw [compressPoly_fold]
  exact (idxSetFold_spec (fun i => compress d p[i]!) 256 zeroPoly).2 j hj
    (by simp [zeroPoly]; omega)

/-! ## §3 — K-PKE DECRYPTION CORRECTNESS at full dimension, from the noise window. -/

/-- **`Compress₁(w) = ByteDecode₁(m)`** — coefficient by coefficient, over the real `ℤ_q`, whenever every
decryption-noise coefficient is inside the `⌊q/4⌋` window. `MlKemCorrect.compress1_recover_zmod` does the
per-coefficient interval arithmetic on the ACTUAL `MlKemCodec.compress`; the casts move the executable's
`Nat` modular ops into `ZMod 3329`. -/
theorem compress_w_eq_msgPoly (dkPke c m : List UInt8)
    (hwin : noiseWindow (kpkeW dkPke c) (msgPoly m) = true) :
    compressPoly 1 (kpkeW dkPke c) = msgPoly m := by
  refine arrayExtAll _ _ (by rw [compressPoly_size, msgPoly_size]) ?_
  intro j hj
  rw [compressPoly_size] at hj
  rw [compressPoly_getElem 1 _ j hj]
  -- names
  set w := kpkeW dkPke c with hw
  set mp := msgPoly m with hmp
  have hwq : w[j]! < 3329 := kpkeW_lt dkPke c j
  have hb2 : mp[j]! < 2 := msgPoly_lt2 m j hj
  have hbq : mp[j]! < 3329 := by omega
  set e := noiseAt w mp j with he
  obtain ⟨hlo, hhi⟩ := noiseWindow_at w mp hwin j hj
  -- the `ℤ_q` identity `w_j = m_j·1665 + e_j`
  have hcong : (w[j]! : ZMod 3329) = (mp[j]! : ZMod 3329) * 1665 + ((e : ℤ) : ZMod 3329) := by
    have hmul : mulModQ (mp[j]!) 1665 < 3329 := MlKemRing.mulModQ_lt _ _
    have hcast : ((subQ (w[j]!) (mulModQ (mp[j]!) 1665) : Nat) : ZMod 3329)
        = (w[j]! : ZMod 3329) - ((mulModQ (mp[j]!) 1665 : Nat) : ZMod 3329) :=
      cast_subQ' _ _ hmul
    rw [he, noiseAt, centeredQ_cast, hcast, cast_mulModQ']
    push_cast
    ring
  -- feed the per-coefficient recovery lemma
  have hbits : ((mp[j]! : ℕ) : ZMod 3329) = 0 ∨ ((mp[j]! : ℕ) : ZMod 3329) = 1 := by
    interval_cases h : mp[j]!
    · left; simp
    · right; simp
  have hrec := MlKemCorrect.compress1_recover_zmod
    ((mp[j]! : ℕ) : ZMod 3329) ((w[j]! : ℕ) : ZMod 3329) hbits e hlo hhi hcong
  rw [ZMod.val_natCast_of_lt hwq, ZMod.val_natCast_of_lt hbq] at hrec
  exact hrec

/-- **K-PKE DECRYPTION CORRECTNESS at ML-KEM-768 dimension.** With the decryption noise inside the FIPS 203
window, `K-PKE.Decrypt(dkPke, c)` returns the 32-byte message `m` exactly. `Compress₁(w) = ByteDecode₁(m)`
(above) then `ByteEncode₁ ∘ ByteDecode₁ = id` (§1). Kernel-clean; no `native_decide`. -/
theorem kpkeDecrypt_recovers (dkPke c m : List UInt8) (hm : m.length = 32)
    (hwin : noiseWindow (kpkeW dkPke c) (msgPoly m) = true) :
    kpkeDecrypt dkPke c = m := by
  rw [kpkeDecrypt_eq, compress_w_eq_msgPoly dkPke c m hwin, byteEncode₁_byteDecode₁ m hm]

/-! ## §4 — the FO/KEM layer: `ML-KEM.Decaps ∘ ML-KEM.Encaps = id` from K-PKE correctness. -/

/-- The `ek` embedded in a decapsulation key (`dk = dk_pke ‖ ek ‖ H(ek) ‖ z`). -/
def ekOfDk (dk : List UInt8) : List UInt8 := (dkDecode dk).2.1

/-- The `dk_pke = ByteEncode₁₂(ŝ)` prefix of a decapsulation key (bytes `[0, 1152)`). -/
def dkPkeOf (dk : List UInt8) : List UInt8 :=
  (dk.toArray.extract 0 (paramK * polyBytes dCoeff)).toList

/-- The K-PKE encryption coins ML-KEM derandomises from the message: `r = G(m ‖ H(ek))[32:]`. -/
def coinsOf (ek m : List UInt8) : List UInt8 := (sha3_512 (m ++ sha3_256 ek)).drop 32

/-- The ciphertext honest encapsulation produces (`c = K-PKE.Encrypt(ek, m, r)`). -/
def ctOf (ek m : List UInt8) : List UInt8 := kpkeEncrypt ek m (coinsOf ek m)

theorem mlkemEncaps_ct (ek m : List UInt8) : (mlkemEncaps ek m).1 = ctOf ek m := rfl

theorem mlkemEncaps_key (ek m : List UInt8) :
    (mlkemEncaps ek m).2 = (sha3_512 (m ++ sha3_256 ek)).take 32 := rfl

/-- **WELL-FORMED decapsulation key** — the embedded hash field really IS `H(ek)` for the embedded `ek`
(FIPS 203 `dk = dk_pke ‖ ek ‖ H(ek) ‖ z`, as `ML-KEM.KeyGen` builds it). A `Bool`, so it is checkable. -/
def wfDk (dk : List UInt8) : Bool := (dkDecode dk).2.2.1 == sha3_256 (ekOfDk dk)

theorem mlkemDecaps_eq (dk c : List UInt8) :
    mlkemDecaps dk c =
      (let m' := kpkeDecrypt (dkPkeOf dk) c
       let g := sha3_512 (m' ++ (dkDecode dk).2.2.1)
       if kpkeEncrypt (ekOfDk dk) m' (g.drop 32) == c then g.take 32
       else Keccak.shake256 ((dkDecode dk).2.2.2 ++ c) 32) := by
  unfold mlkemDecaps ekOfDk dkPkeOf
  simp only [Id.run]
  rfl

/-- **THE FULL-DIMENSION FO ROUND TRIP.** On a well-formed ML-KEM-768 decapsulation key, `ML-KEM.Decaps`
returns EXACTLY `ML-KEM.Encaps`'s shared secret — given only that K-PKE decryption recovers the message. The
whole Fujisaki–Okamoto layer is DERIVED: `m' = m` makes the two `G = SHA3-512` calls identical, so the
re-encryption coins `r'` equal the encapsulation coins `r`, so `c'` is literally the same `kpkeEncrypt` call
that produced `c`, so the byte-exact FO gate fires and `K' = K`. (A tampered `c` misses the gate and takes the
implicit-reject branch `J(z‖c)` — that direction is `MlKemDecaps.decaps_rejects_tampered`.) -/
theorem mlkem_roundtrip_of_kpke (dk m : List UInt8) (hwf : wfDk dk = true)
    (hdec : kpkeDecrypt (dkPkeOf dk) (ctOf (ekOfDk dk) m) = m) :
    mlkemDecaps dk (mlkemEncaps (ekOfDk dk) m).1 = (mlkemEncaps (ekOfDk dk) m).2 := by
  have hh : (dkDecode dk).2.2.1 = sha3_256 (ekOfDk dk) := by
    simpa [wfDk] using hwf
  rw [mlkemEncaps_ct, mlkemEncaps_key, mlkemDecaps_eq]
  simp only [hdec, hh]
  -- now `c' = kpkeEncrypt ek m (coinsOf ek m) = ctOf ek m = c`, so the FO gate fires.
  rw [show (sha3_512 (m ++ sha3_256 (ekOfDk dk))).drop 32 = coinsOf (ekOfDk dk) m from rfl,
    show kpkeEncrypt (ekOfDk dk) m (coinsOf (ekOfDk dk) m) = ctOf (ekOfDk dk) m from rfl]
  simp

/-! ## §5 — the FULL-DIMENSION `DreggKemApi` and `Fips203Correct` at ML-KEM-768. -/

/-- **THE ML-KEM-768 "no decryption failure" EVENT at key `dk`, message `m`** — the key is well-formed AND
the executable pipeline's decryption noise stays inside the FIPS 203 `⌊q/4⌋` window at every one of the 256
coefficients. This is EXACTLY the event `MlKemCorrect.decryptCorrect_conditional` needs and `MlKemDelta`
bounds the complement of (`≤ δ`, §6). ML-KEM is `δ`-correct, not perfectly correct: keys outside this event
genuinely DO fail to decapsulate, so the honest full-dimension `Fips203Correct` is stated over them. -/
def goodKey (m dk : List UInt8) : Bool :=
  wfDk dk && noiseWindow (kpkeW (dkPkeOf dk) (ctOf (ekOfDk dk) m)) (msgPoly m)

/-- The decapsulation-key type of the full-dimension API: 2400-byte ML-KEM-768 keys satisfying `goodKey`. -/
def Dk768 (m : List UInt8) : Type := { dk : List UInt8 // goodKey m dk = true }

/-- **THE FULL-DIMENSION `dregg-pq` HYBRID-KEM API.** The ML-KEM half is the REAL ML-KEM-768: `mlkem_encaps`
is `MlKemEncaps.mlkemEncaps` (`ek : 1184 B → (ct : 1088 B, K : 32 B)`, the byte-exact FO encapsulation proved
equal to the `ml-kem` crate's), `mlkem_decaps` is `MlKemDecaps.mlkemDecaps` (the full FO decapsulation with
re-encryption + implicit reject), `ekOf` reads the `ek` out of the `dk` blob. `transcript` is the genuine
public concatenation and `combine` the concat-KDF shape (SHA3-256 over `ss_x ‖ ss_pq ‖ transcript`) — the
X-Wing combiner's form. The X25519 half stays the commutative toy (`X25519Correct` is a SEPARATE trusted
floor / separate lane; `DreggKemRefinement.badDh_breaks_correctness` shows it is load-bearing). -/
def fullKemApi (m : List UInt8) :
    DreggKemApi ℕ ℕ (Dk768 m) (List UInt8) (List UInt8) (List UInt8) (List UInt8) where
  x25519_pk sk := sk
  x25519_dh a b := [UInt8.ofNat (a * b % 256)]
  ekOf dk := ekOfDk dk.1
  mlkem_encaps ek := mlkemEncaps ek m
  mlkem_decaps dk c := mlkemDecaps dk.1 c
  transcript xa ek xb ct := [UInt8.ofNat (xa % 256)] ++ ek ++ [UInt8.ofNat (xb % 256)] ++ ct
  combine k1 k2 tr := sha3_256 (k1 ++ k2 ++ tr)

/-- **`Fips203Correct` AT REAL ML-KEM-768 PARAMETERS.** For EVERY ML-KEM-768 decapsulation key in the
`δ`-correct set, decapsulating the honest 1088-byte encapsulation recovers the encapsulated 32-byte shared
secret. The `Fips203Correct` DEFINITION is untouched (`DreggKemRefinement`); what changed is that it is now
instantiated at `k = 3`, `n = 256`, `q = 3329`, `η₁ = η₂ = 2`, `d_u = 10`, `d_v = 4` — the full negacyclic
ring, the incomplete Kyber NTT, the CBD sampler, both compression codecs, SHA3/SHAKE — instead of the
`n = 1`, `A = 1` scalar toy. Kernel-clean: no `native_decide`, no `sorry`. -/
theorem fullKemApi_fips203 (m : List UInt8) (hm : m.length = 32) : Fips203Correct (fullKemApi m) := by
  rintro ⟨dk, hgood⟩
  simp only [goodKey, Bool.and_eq_true] at hgood
  simp only [fullKemApi]
  exact mlkem_roundtrip_of_kpke dk m hgood.1
    (kpkeDecrypt_recovers _ _ m hm hgood.2)

/-- The X25519 half of the full-dimension API agrees (the commutative toy DH — the REAL X25519 floor is the
separate lane, exactly as in `DreggKemRefinement`). -/
theorem fullKemApi_x25519 (m : List UInt8) : X25519Correct (fullKemApi m) := by
  intro a b; simp only [fullKemApi]; rw [Nat.mul_comm]

/-- **THE DEPLOYED THEOREM, FED A FULL-DIMENSION FLOOR.** `DreggKemRefinement.dregg_kem_correct` — the
`dregg-pq` hybrid handshake's key-agreement theorem — instantiated at the REAL ML-KEM-768 API: initiator and
responder derive the SAME session key, with the FIPS 203 round trip DISCHARGED at full dimension rather than
assumed (and rather than discharged at the `n = 1` toy). -/
theorem fullKemApi_agrees (m : List UInt8) (hm : m.length = 32)
    (xskr : ℕ) (dk : Dk768 m) (xski : ℕ) :
    initKey (fullKemApi m) ((fullKemApi m).x25519_pk xskr) ((fullKemApi m).ekOf dk) xski
      = finishKey (fullKemApi m) xskr dk ((fullKemApi m).x25519_pk xski)
          ((fullKemApi m).mlkem_encaps ((fullKemApi m).ekOf dk)).1 :=
  dregg_kem_correct (fullKemApi m) (fullKemApi_x25519 m) (fullKemApi_fips203 m hm) xskr dk xski

/-! ## §6 — WIRED TO `MlKemDelta`: the round trip fails with probability `≤ δ`.

`MlKemDelta` bounds — unconditionally, in-kernel, by the exact-MGF Chernoff route over the real CBD noise —
the probability that the modeled ML-KEM-768 `e_total` ENVELOPE `mlkemZ` escapes the `(−832, 832)` window at
ANY coefficient. Since `goodKey` is EXACTLY "in-window everywhere" (plus key well-formedness), a key sampler
whose true decaps-failure event is DOMINATED by the envelope's failure event inherits the bound — by `winProb`
monotonicity.

**The δ-level is a THREADED, NAMED OBLIGATION (`EnvelopeDeltaBound δ`), never a `sorry`.** The transport
theorem `roundtrip_fails_le_delta` is stated ∀ δ and takes the envelope bound as an EXPLICIT HYPOTHESIS, so
this module states exactly what it assumes and each tree may discharge it at the strongest δ it actually
proves. `roundtrip_fails_le_delta_2pow140` is the UNCONDITIONAL instance every tree can close, from
`MlKemDelta.mlkem768_decapsFailure_le_delta_unconditional` (`δ = 2⁻¹⁴⁰`); on trees carrying the tightened
`MlKemDelta.mlkem768_decapsFailure_le_delta_unconditional_tight`, feeding THAT to the same theorem yields
`δ = 2⁻¹⁴⁸` with no other change. Nothing here re-asserts an analytic result it does not have: the Chernoff /
union analysis is `MlKemDelta`'s, and its availability is visible in the hypothesis, not hidden. -/

/-- `winProb` is monotone in the winning predicate (a bigger favorable set has bigger counting probability). -/
theorem winProb_mono {Ω : Type*} [Fintype Ω] (p r : Ω → Bool) (h : ∀ ω, p ω = true → r ω = true) :
    winProb p ≤ winProb r := by
  unfold winProb
  have hcard : (Finset.univ.filter (fun o => p o = true)).card
      ≤ (Finset.univ.filter (fun o => r o = true)).card :=
    Finset.card_le_card (fun o ho => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
      exact h o ho)
  have hc : ((Finset.univ.filter (fun o => p o = true)).card : ℝ)
      ≤ ((Finset.univ.filter (fun o => r o = true)).card : ℝ) := by exact_mod_cast hcard
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

/-- **THE NAMED δ-OBLIGATION.** `EnvelopeDeltaBound δ` says the MODELED ML-KEM-768 noise envelope `mlkemZ`
escapes the `(−832, 832)` window at some coefficient with probability at most `δ`.

This is the hard ANALYTIC result — exact-MGF Chernoff per coefficient plus the `768`-term union bound — and it
is NOT proved in this module. It is `Dregg2.Crypto.MlKemDelta`'s: `mlkem768_decapsFailure_le_delta_unconditional`
closes it at `δ = 2⁻¹⁴⁰` (available on every tree), and the tightened
`mlkem768_decapsFailure_le_delta_unconditional_tight` at `δ = 2⁻¹⁴⁸` where present. Naming it as a `Prop` and
THREADING it as a hypothesis (rather than `sorry`-ing it, or re-declaring it as an `axiom` this project already
proves elsewhere) is what keeps this module's assumption set visible and greppable. -/
def EnvelopeDeltaBound (δ : ℝ) : Prop :=
  winProb (MlKemDelta.decapsFails MlKemDelta.mlkemZ) ≤ δ

/-- **THE `δ`-WIRED FULL-DIMENSION CORRECTNESS.** For ANY `δ` bounding the envelope's failure probability
(`hδ : EnvelopeDeltaBound δ` — the NAMED analytic obligation, supplied by `MlKemDelta`, see above) and ANY
sampler of well-formed ML-KEM-768 decapsulation keys whose true decaps-failure event is DOMINATED by the
envelope model's failure event (`hdom` — the ONE named residual, see the header: whenever the envelope `mlkemZ`
registers NO failure at `ω`, the executable pipeline's noise is in-window at every coefficient), the
FULL-DIMENSION encaps→decaps round trip FAILS with probability `≤ δ`. So `Fips203Correct` holds at real
ML-KEM-768 parameters except with probability `≤ δ` — which is exactly what FIPS 203 correctness asserts.

The CONTENT proved here is the TRANSPORT — `winProb` monotonicity through the domination, plus the executable
`mlkem_roundtrip_of_kpke`/`kpkeDecrypt_recovers` chain — not the δ-bound itself.

`hdom` is the honest replacement for the earlier (FALSE, hence vacuous) equality hypothesis `hbridge`:
`mlkemZ` is a conservative MGF-envelope (`±104` `Δv`, `cbd²` products), so it DOMINATES rather than EQUALS the
literal noise. `roundtrip_fails_le_delta_nonvacuous` (§7) exhibits a sampler satisfying `hdom`, so this is not
vacuous. -/
theorem roundtrip_fails_le_delta (δ : ℝ) (hδ : EnvelopeDeltaBound δ)
    (m : List UInt8) (hm : m.length = 32)
    (key : MlKemDelta.mlkemΩ → List UInt8)
    (hwf : ∀ ω, wfDk (key ω) = true)
    (hdom : ∀ ω, MlKemDelta.decapsFails MlKemDelta.mlkemZ ω = false →
        noiseWindow (kpkeW (dkPkeOf (key ω)) (ctOf (ekOfDk (key ω)) m)) (msgPoly m) = true) :
    winProb (fun ω => decide (mlkemDecaps (key ω) (mlkemEncaps (ekOfDk (key ω)) m).1
        ≠ (mlkemEncaps (ekOfDk (key ω)) m).2))
      ≤ δ := by
  refine le_trans (winProb_mono _ (MlKemDelta.decapsFails MlKemDelta.mlkemZ) ?_) hδ
  intro ω hfail
  by_contra hne
  -- the envelope registered NO failure at `ω` …
  have hfalse : MlKemDelta.decapsFails MlKemDelta.mlkemZ ω = false := Bool.not_eq_true _ |>.mp hne
  -- … so, by DOMINATION, the executable pipeline's noise is in-window everywhere …
  have hwin := hdom ω hfalse
  -- … so the round trip SUCCEEDS, contradicting the failure predicate.
  have hrt := mlkem_roundtrip_of_kpke (key ω) m (hwf ω)
    (kpkeDecrypt_recovers _ _ m hm hwin)
  rw [decide_eq_true_eq] at hfail
  exact hfail hrt

/-- **THE UNCONDITIONAL INSTANCE THIS TREE CLOSES — `δ = 2⁻¹⁴⁰`.** `roundtrip_fails_le_delta` fed the
assumption-free envelope bound `MlKemDelta.mlkem768_decapsFailure_le_delta_unconditional`. No hypothesis on the
δ-level survives; `hdom` (the domination residual) is the only one left, exactly as in §6's header. On trees
carrying `MlKemDelta.mlkem768_decapsFailure_le_delta_unconditional_tight`, the SAME theorem instantiated at
that bound gives `δ = 2⁻¹⁴⁸`. -/
theorem roundtrip_fails_le_delta_2pow140 (m : List UInt8) (hm : m.length = 32)
    (key : MlKemDelta.mlkemΩ → List UInt8)
    (hwf : ∀ ω, wfDk (key ω) = true)
    (hdom : ∀ ω, MlKemDelta.decapsFails MlKemDelta.mlkemZ ω = false →
        noiseWindow (kpkeW (dkPkeOf (key ω)) (ctOf (ekOfDk (key ω)) m)) (msgPoly m) = true) :
    winProb (fun ω => decide (mlkemDecaps (key ω) (mlkemEncaps (ekOfDk (key ω)) m).1
        ≠ (mlkemEncaps (ekOfDk (key ω)) m).2))
      ≤ (2 : ℝ) ^ (-140 : ℤ) :=
  roundtrip_fails_le_delta _ MlKemDelta.mlkem768_decapsFailure_le_delta_unconditional m hm key hwf hdom

/-! ## §7 — NON-VACUITY: the GENUINE `ml-kem` v0.2.3 crate key INHABITS the `δ`-correct set.

The ONLY `native_decide` in this file, and it is a concrete byte check (`goodKey` is a `Bool` over the pinned
2400-byte crate `dk` and the 1088-byte ciphertext its encapsulation produces) — it does NOT appear in the
axiom set of any ∀-theorem above. Its trusted base is `Lean.ofReduceBool` + `Lean.trustCompiler`, the residual
`MlKemCodec` / `MlKemDecaps` / `MlKemEncaps` / `Keccak` already name. -/

/-- The pinned NIST ACVP encapsulation message is the 32 bytes ML-KEM requires. -/
theorem acvpM_len : MlKemEncaps.acvpM.toList.length = 32 := by decide

/-- The `ek` embedded in the REAL crate `dk` IS the REAL crate `ek` (the `dk_pke ‖ ek ‖ H(ek) ‖ z` layout). -/
theorem ekOfDk_realDk : ekOfDk realDk.toList = realEk.toList := by native_decide

/-- **NON-VACUITY**: the GENUINE `ml-kem` v0.2.3 crate decapsulation key is well-formed AND its decryption
noise is inside the FIPS 203 window at all 256 coefficients — so the `δ`-correct key set is INHABITED and
`fullKemApi_fips203` is not vacuous. A concrete byte check (`native_decide`, isolated). -/
theorem realDk_good : goodKey MlKemEncaps.acvpM.toList realDk.toList = true := by native_decide

/-- The real crate key, as an inhabitant of the full-dimension API's decapsulation-key type. -/
def realDk768 : Dk768 MlKemEncaps.acvpM.toList := ⟨realDk.toList, realDk_good⟩

/-- **THE FULL-DIMENSION ROUND TRIP, ON THE REAL CRATE KEY** — `fullKemApi_fips203` FIRES: ML-KEM-768 decaps of
the honest 1088-byte encapsulation under the genuine `ml-kem` crate key recovers the encapsulated 32-byte
secret. (`MlKemEncaps.encaps_decaps_roundtrip` checks the same fact by compiled evaluation; here it is a
CONSEQUENCE of the ∀-theorem, which is the point.) -/
theorem realDk_roundtrip :
    mlkemDecaps realDk.toList (mlkemEncaps (ekOfDk realDk.toList) MlKemEncaps.acvpM.toList).1
      = (mlkemEncaps (ekOfDk realDk.toList) MlKemEncaps.acvpM.toList).2 := by
  have h := fullKemApi_fips203 MlKemEncaps.acvpM.toList acvpM_len realDk768
  simpa only [fullKemApi, realDk768] using h

/-- **TOOTH — `goodKey` is REFUTABLE.** An all-zero 2400-byte `dk` (embedded hash field ≠ `H(ek)`) is NOT in
the `δ`-correct set: `goodKey` genuinely rejects (`wfDk` fails), so it is not `fun _ _ => true`. -/
theorem zeroDk_not_good : goodKey MlKemEncaps.acvpM.toList (List.replicate 2400 (0 : UInt8)) = false := by
  native_decide

/-- **NON-VACUITY of the `δ`-WIRED CORRECTNESS.** The domination hypothesis `hdom` of `roundtrip_fails_le_delta`
is SATISFIABLE — the constant sampler at the genuine `ml-kem` crate key discharges it (there the true noise is
in-window at every coefficient, so `hdom` holds vacuously in its antecedent and δ transports). This is the
concrete improvement over the earlier (FALSE, hence unsatisfiable) equality hypothesis `hbridge`: the reformulated
theorem is NOT vacuous. Carries the `native_decide` residual of `realDk_good`, so it is NOT in the clean list. -/
theorem roundtrip_fails_le_delta_nonvacuous :
    winProb (fun _ : MlKemDelta.mlkemΩ =>
        decide (mlkemDecaps realDk.toList
            (mlkemEncaps (ekOfDk realDk.toList) MlKemEncaps.acvpM.toList).1
          ≠ (mlkemEncaps (ekOfDk realDk.toList) MlKemEncaps.acvpM.toList).2))
      ≤ (2 : ℝ) ^ (-140 : ℤ) := by
  have hgood := realDk_good
  simp only [goodKey, Bool.and_eq_true] at hgood
  exact roundtrip_fails_le_delta_2pow140 MlKemEncaps.acvpM.toList acvpM_len
    (fun _ => realDk.toList) (fun _ => hgood.1) (fun _ _ => hgood.2)

/-! ## §8 — REUSABLE CORE toward DISCHARGING `hdom`: `intt`-linearity + `ntt ∘ intt = id`, and the NAMED
remaining faithfulness pieces.

Fully discharging `hdom` (§6) — rather than hypothesizing it — means exhibiting the executable pipeline's noise
`noiseAt (kpkeW dkPke c) (msgPoly m)` as `MlKemCorrect.eTotal` (so `MlKemCorrect.mlkem_decrypt_cancellation`
applies), then running the §13 byte-faithful MGF-domination (`MlKemDelta.bf*`) on that literal noise. The
cancellation is proved over an ABSTRACT `[CommRing R]`; transporting it to the executable `Array Nat` pipeline
factors through the NTT algebra. The two REUSABLE legs are proved here:

* `intt_addLinear` — `intt` is additive over `addPoly` (coefficient-wise in `ℤ_q`). Immediate from the
  interpolation formula `MlKemNttFaithful.intt_interp_kem` (the `intt` coefficient is a `ℤ_q`-LINEAR functional
  of the input coefficients) + `cast_addPoly`. This is what lets `intt` distribute over the K-PKE accumulator
  `∑ᵢ pointwiseNtt(ŝᵢ, ntt uᵢ)`.
* `ntt_intt_rightInverse` — `ntt ∘ intt = id` on canonical reduced polys, the OTHER direction of the proved
  `MlKemNttFaithful.ntt_intt_id` (`intt ∘ ntt = id`). Derived by a FINITENESS/bijection argument: on the finite
  set of canonical reduced polys, `intt ∘ ntt = id` makes `ntt` injective, hence (finite) bijective, hence its
  left inverse `intt` is a two-sided inverse. This is what turns a stored NTT-domain secret `ŝᵢ` into
  `ntt(intt ŝᵢ)`, so `ntt_computes_negacyclic_mul` applies to the accumulator terms.

STATUS (each named precisely):
1. **`Poly → R_q` coefficient RING hom + the LITERAL cancellation — DISCHARGED (§8.8).** The `CommRing R_q =
   AdjoinRoot(X²⁵⁶+1)` carrying `schoolbookMul` as `*` ALREADY EXISTS as `DecapsCoreSpec.Rq_kem` /
   `toRqKem_schoolbookMul`; `kpkeW_toRqKem` exhibits `toRqKem (kpkeW) = v − Σⱼ sⱼ·uⱼ` over that ring (the honest-key
   obligation discharged by `ntt_intt_rightInverse`), and `kpkeW_toRqKem_cancellation` composes it with
   `MlKemCorrect.mlkem_decrypt_cancellation` at `R = Rq_kem` to reach the LITERAL `toRqKem (kpkeW) = μ + e_total`,
   under the abstract-model identifications of `v, u, s` (the payload of 2/3/4). (`phiCoeff`, §8.4, is only
   ADDITIVE and does NOT suffice — the multiplicative cancellation needs this genuine ring.)
2. **byte-codec faithfulness** — `ŝ = ByteDecode₁₂(dk_pke)`, `(u,v) = ctDecode c` after `Decompress_{du}`/
   `Decompress_{dv}` really are the ring elements `s`, `u = Aᵀr+e1+Δu`, `v = tᵀr+e2+μ+Δv` of `MlKemCorrect`
   (size/reduced legs closed: `sHatOf_lt`, `uOf_size`; the encrypt-side ring algebra is
   `EncapsCoreSpec.encrypt_{u,v}_ring_faithful` over this same `Rq_kem`).
3. **`ExpandA`** — the `SampleNTT`/`XOF` public-matrix expansion `A` matches the abstract `A : Fin k → Fin k → R`
   (NAMED `ExpandAFaithful`, §8.7). Genuinely blocked on the rejection-sampling FILL (that `SampleNTT` yields
   exactly 256 accepted `<q` coefficients is NOT a `∀`-theorem — it is the probabilistic fill event; the
   branching-`forIn` reducedness invariant is not built).
4. **CBD samplers — structural + bit-extraction faithfulness DISCHARGED (§8.9).** `samplePolyCBD_size` /
   `samplePolyCBD_lt` / `samplePolyCBD_getElem` prove `SamplePolyCBD(η)` is canonical in `R_q` and its `j`-th
   coefficient IS the FIPS 203 Alg 8 centered bit-difference `subQ (Σ bit) (Σ bit)`; the sole residual is the
   DISTRIBUTIONAL tie to the CBD noise `MlKemDelta` models (sibling-owned, `CbdFaithful`, §8.7). -/

/-! ### §8.1 — `intt` preserves the canonical (size-256, reduced) shape (needed for the bijection). -/

/-- `intt` keeps a canonical reduced poly size-256. Mirrors `nttLeftInverse_proven`'s size step. -/
theorem intt_size (w : Poly) (hw : w.size = 256) (hwlt : ∀ (p : Nat), w[p]! < q) :
    (intt w).size = 256 := by
  have h7sz : (MlKemRing.kInttUpto 7 w).1.size = 256 :=
    (MlKemRing.kInttStage_inv w hw hwlt 7 (by omega)).1
  rw [MlKemRing.intt_eq_scale_stages, MlKemRing.kInttStages_eq]
  exact MlKemRing.kInttScale_size _ h7sz

/-- `intt` keeps a canonical reduced poly reduced (`< q` everywhere): the final `128⁻¹` scaling writes a
`mulModQ`-reduced value to every coefficient. -/
theorem intt_lt (w : Poly) (hw : w.size = 256) (hwlt : ∀ (p : Nat), w[p]! < q) :
    ∀ (p : Nat), (intt w)[p]! < q := by
  have h7sz : (MlKemRing.kInttUpto 7 w).1.size = 256 :=
    (MlKemRing.kInttStage_inv w hw hwlt 7 (by omega)).1
  have hisz : (intt w).size = 256 := intt_size w hw hwlt
  intro p
  by_cases hp : p < 256
  · rw [MlKemRing.intt_eq_scale_stages, MlKemRing.kInttStages_eq,
        MlKemRing.kInttScale_getElem _ h7sz p hp]
    exact MlKemRing.mulModQ_lt _ _
  · rw [MlKemRing.getElem!_ge (intt w) p (by rw [hisz]; omega)]
    unfold MlKemRing.q; omega

/-! ### §8.2 — `intt`-LINEARITY over `addPoly` (from the interpolation formula). -/

/-- **`intt`-linearity at a pair index** `2i+r`: the `intt` coefficient of `addPoly a b` is the `ℤ_q`-sum of the
`intt` coefficients of `a` and `b`. Direct from `intt_interp_kem` (the coefficient is a linear functional of the
inputs) + `cast_addPoly`. -/
theorem intt_addLinear_pair (a b : Poly) (ha : a.size = 256) (halt : ∀ (p : Nat), a[p]! < q)
    (hb : b.size = 256) (hblt : ∀ (p : Nat), b[p]! < q) (i r : Nat) (hi : i < 128) (hr : r < 2) :
    ((intt (addPoly a b))[2*i+r]! : ZMod q)
      = ((intt a)[2*i+r]! : ZMod q) + ((intt b)[2*i+r]! : ZMod q) := by
  have hab : (addPoly a b).size = 256 := MlKemRing.addPoly_size a b
  have hablt : ∀ (p : Nat), (addPoly a b)[p]! < q := MlKemRing.addPoly_lt a b
  -- the `intt` coefficient is a `ℤ_q`-LINEAR functional of the inputs; split the sum termwise.
  have hsum : (∑ u ∈ Finset.range 128, ((addPoly a b)[2*u+r]! : ZMod q) * (MlKemRing.kirt u)^i)
      = (∑ u ∈ Finset.range 128, (a[2*u+r]! : ZMod q) * (MlKemRing.kirt u)^i)
        + (∑ u ∈ Finset.range 128, (b[2*u+r]! : ZMod q) * (MlKemRing.kirt u)^i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hu256 : 2*u+r < 256 := by have := Finset.mem_range.mp hu; omega
    rw [MlKemRing.cast_addPoly a b (2*u+r) hu256, add_mul]
  rw [MlKemRing.intt_interp_kem (addPoly a b) hab hablt i r hi hr,
      MlKemRing.intt_interp_kem a ha halt i r hi hr,
      MlKemRing.intt_interp_kem b hb hblt i r hi hr, hsum, mul_add]

/-- **`intt`-LINEARITY (all coefficients)** — `φ(intt(addPoly a b)) = φ(intt a) + φ(intt b)` coefficient-wise in
`ℤ_q`, for canonical reduced `a, b`. The reusable additivity that distributes `intt` over the K-PKE decryption
accumulator. -/
theorem intt_addLinear (a b : Poly) (ha : a.size = 256) (halt : ∀ (p : Nat), a[p]! < q)
    (hb : b.size = 256) (hblt : ∀ (p : Nat), b[p]! < q) (p : Nat) (hp : p < 256) :
    ((intt (addPoly a b))[p]! : ZMod q)
      = ((intt a)[p]! : ZMod q) + ((intt b)[p]! : ZMod q) := by
  rcases Nat.even_or_odd p with ⟨i, hpe⟩ | ⟨i, hpo⟩
  · have hpi : p = 2*i+0 := by omega
    rw [hpi]; exact intt_addLinear_pair a b ha halt hb hblt i 0 (by omega) (by norm_num)
  · have hpi : p = 2*i+1 := by omega
    rw [hpi]; exact intt_addLinear_pair a b ha halt hb hblt i 1 (by omega) (by norm_num)

/-! ### §8.3 — `ntt ∘ intt = id` on canonical reduced polys (the finiteness/bijection dual of `ntt_intt_id`). -/

/-- The canonical-poly predicate: size 256 and every coefficient reduced (`< q`). -/
abbrev IsCanPoly (c : Poly) : Prop := c.size = 256 ∧ (∀ (p : Nat), getElem! c p < q)

/-- The finite domain the incomplete NTT bijects: canonical (size-256) reduced (`< q`) polys. -/
abbrev CanPoly : Type := { c : Poly // IsCanPoly c }

/-- `CanPoly` is FINITE — the reduced `ℤ_q` coefficient reading `CanPoly ↪ (Fin 256 → ZMod q)` is injective
(`arrayExtAll` + `natCast_inj_of_lt` on the reduced coefficients), and the codomain is a `Fintype`. -/
instance : Finite CanPoly :=
  Finite.of_injective (β := Fin 256 → ZMod q)
    (fun c i => ((c.1[(i : Nat)]! : ZMod q)))
    (by
      intro x y hxy
      apply Subtype.ext
      refine arrayExtAll x.1 y.1 (by rw [x.2.1, y.2.1]) ?_
      intro j hj
      have hj256 : j < 256 := by rw [x.2.1] at hj; exact hj
      have hcong := congrFun hxy ⟨j, hj256⟩
      exact MlKemRing.natCast_inj_of_lt _ _ (x.2.2 j) (y.2.2 j) hcong)

/-- `ntt` as an endofunction of `CanPoly` (`ntt_size`/`ntt_lt` keep the shape). -/
def nttC (c : CanPoly) : CanPoly := ⟨ntt c.1, MlKemRing.ntt_size c.1 c.2.1, MlKemRing.ntt_lt c.1 c.2.2⟩

/-- `intt` as an endofunction of `CanPoly` (§8.1). -/
def inttC (c : CanPoly) : CanPoly := ⟨intt c.1, intt_size c.1 c.2.1 c.2.2, intt_lt c.1 c.2.1 c.2.2⟩

/-- `intt ∘ ntt = id` on `CanPoly` (= `ntt_intt_id`/`nttLeftInverse_proven`, lifted to the subtype). -/
theorem inttC_nttC (c : CanPoly) : inttC (nttC c) = c :=
  Subtype.ext (MlKemRing.nttLeftInverse_proven c.1 c.2.1 c.2.2)

/-- **`ntt ∘ intt = id` on canonical reduced polys** — the reverse direction of `ntt_intt_id`. On the FINITE set
`CanPoly`, `inttC ∘ nttC = id` (`inttC_nttC`) makes `nttC` injective, hence bijective, hence its left inverse
`inttC` is a two-sided inverse; reading off the `Array` value gives `ntt (intt d) = d`. This is the reusable leg
that turns a stored NTT-domain secret `ŝ` into `ntt (intt ŝ)`, so `ntt_computes_negacyclic_mul` applies. -/
theorem ntt_intt_rightInverse (d : Poly) (hd : d.size = 256) (hdlt : ∀ (p : Nat), d[p]! < q) :
    ntt (intt d) = d := by
  have hLI : Function.LeftInverse inttC nttC := inttC_nttC
  have hInj : Function.Injective nttC := hLI.injective
  have hSurj : Function.Surjective nttC := (Finite.injective_iff_surjective).mp hInj
  obtain ⟨c, hc⟩ := hSurj ⟨d, hd, hdlt⟩
  have hid : inttC ⟨d, hd, hdlt⟩ = c := by rw [← hc]; exact hLI c
  have hR : nttC (inttC ⟨d, hd, hdlt⟩) = ⟨d, hd, hdlt⟩ := by rw [hid]; exact hc
  exact congrArg Subtype.val hR

/-! ### §8.4 — the COEFFICIENT RING HOM `φ : Poly → (Fin 256 → ℤ_q)` and its additivity.

`φ` reads the 256 `ℤ_q` coefficients. It respects `addPoly` (`cast_addPoly`, §RUNG-1) — the reusable
additive structure the K-PKE decryption accumulator `∑ᵢ …` is summed in. On canonical reduced polys it also
carries the executable NTT-domain product to the negacyclic ring product (§8.5, via
`ntt_computes_negacyclic_mul`). -/

/-- The coefficient hom `φ : Poly → (Fin 256 → ZMod q)` — coefficient `c` read into `ℤ_q`. -/
def phiCoeff (p : Poly) : Fin 256 → ZMod q := fun c => ((p[(c : Nat)]! : Nat) : ZMod q)

/-- **`φ` respects `+`** — `φ(addPoly a b) = φ a + φ b`. Immediate from the RUNG-1 cast `cast_addPoly`; this is
the additive-hom property that lets `φ` distribute over the K-PKE decryption accumulator's `∑ᵢ`. -/
theorem phiCoeff_addPoly (a b : Poly) : phiCoeff (addPoly a b) = phiCoeff a + phiCoeff b := by
  funext c
  simp only [phiCoeff, Pi.add_apply]
  exact MlKemRing.cast_addPoly a b (c : Nat) c.isLt

/-! ### §8.5 — the per-term negacyclic reduction and the assembled `φ(kpkeW)`.

The executable K-PKE decrypt builds `w = v − NTT⁻¹(∑ᵢ ŝᵢ ∘ NTT(uᵢ))`. Each accumulator term
`intt (pointwiseNtt ŝᵢ (ntt uᵢ))` (the fast incomplete-NTT multiply of the STORED NTT-domain secret `ŝᵢ` by
`uᵢ`) reduces to the ground-truth negacyclic product `schoolbookMul (intt ŝᵢ) uᵢ` — this is exactly where
`ntt_intt_rightInverse` (§8.3, `ntt (intt ŝᵢ) = ŝᵢ`) and `ntt_computes_negacyclic_mul` combine. `φ` then
distributes over the `∑ᵢ` by `intt_addLinear` (§8.2), exhibiting `φ(kpkeW)` in the `wVal` shape
`φ v − ∑ⱼ φ(sⱼ · uⱼ)` (`MlKemCorrect.wVal`, up to the input identifications §8-(2/3/4)). -/

/-- The stored NTT-domain secret `ŝᵢ = ByteDecode₁₂(dk_pke)` at index `i`. -/
def sHatOf (dkPke : List UInt8) (i : Nat) : Poly :=
  byteDecodeAt dCoeff dkPke.toArray (i * polyBytes dCoeff)

/-- The decompressed ciphertext component `uᵢ` (`ctDecode c` first projection). -/
def uOf (c : List UInt8) (i : Nat) : Poly := (ctDecode c).1[i]!

/-- `ŝᵢ = ByteDecode₁₂(…)` is a canonical `R_q` element: 256 coefficients. -/
theorem sHatOf_size (dkPke : List UInt8) (i : Nat) : (sHatOf dkPke i).size = 256 :=
  byteDecodeAt_size _ _ _

/-- `ŝᵢ` is reduced (`< q` everywhere) — the `ByteDecode₁₂` codomain reduces every 12-bit digit mod `q`; out
of range the reader is `0`. This is the byte-codec faithfulness fact that `ŝ` lands in the ring `R_q`. -/
theorem sHatOf_lt (dkPke : List UInt8) (i : Nat) : ∀ (p : Nat), (sHatOf dkPke i)[p]! < q := by
  intro p
  by_cases hp : p < 256
  · rw [sHatOf, byteDecodeAt_getElem dCoeff _ _ p hp]
    simp only [dCoeff, show ((12 : Nat) == 12) = true from rfl, if_true]
    exact Nat.mod_lt _ (by unfold MlKemRing.q; omega)
  · rw [MlKemRing.getElem!_ge _ p (by rw [sHatOf, byteDecodeAt_size]; omega)]
    unfold MlKemRing.q; omega

/-- **PER-TERM NEGACYCLIC REDUCTION.** The executable accumulator term `intt (pointwiseNtt ŝ (ntt u))` — the
fast incomplete-NTT multiply of the stored NTT-domain secret `ŝ` by `u` — IS the ground-truth negacyclic ring
product `schoolbookMul (intt ŝ) u`. Assembles `ntt_intt_rightInverse` (`ntt (intt ŝ) = ŝ`, so `ŝ` is an
`ntt`-image) with `MlKemNttFaithful`'s ∀-theorem `MlKemRing.mlkem_ntt_ring_faithful` (the fast incomplete-NTT
path IS the negacyclic ring product, for ALL canonical size-256 pairs). We cite `mlkem_ntt_ring_faithful` —
the PROVED ∀-statement itself — rather than the later gate-name alias `ntt_computes_negacyclic_mul`, because
the alias only exists on trees that have already retired `MlKemRing`'s one-sample `native_decide` gate of the
same name; the ∀-theorem it abbreviates is the same term on every tree. -/
theorem intt_pointwiseNtt_ntt (sh u : Poly) (hsh : sh.size = 256) (hshlt : ∀ (p : Nat), sh[p]! < q)
    (hu : u.size = 256) :
    intt (pointwiseNtt sh (ntt u)) = MlKemRing.schoolbookMul (intt sh) u := by
  have hrs : ntt (intt sh) = sh := ntt_intt_rightInverse sh hsh hshlt
  have hisz : (intt sh).size = 256 := intt_size sh hsh hshlt
  calc intt (pointwiseNtt sh (ntt u))
      = intt (pointwiseNtt (ntt (intt sh)) (ntt u)) := by rw [hrs]
    _ = MlKemRing.schoolbookMul (intt sh) u :=
        MlKemRing.mlkem_ntt_ring_faithful (intt sh) u hisz hu

/-- `φ(intt zeroPoly) = 0` coefficient-wise — `intt` of the zero poly has zero `ℤ_q` coefficients (each is
`nInv · ∑ 0 = 0` via `intt_interp_kem`). Base of the accumulator's `∑ᵢ` distribution. -/
theorem intt_zeroPoly_cast (p : Nat) (hp : p < 256) : ((intt zeroPoly)[p]! : ZMod q) = 0 := by
  have hz256 : (zeroPoly : Poly).size = 256 := by simp [zeroPoly]
  have hpair : ∀ i r, i < 128 → r < 2 → ((intt zeroPoly)[2*i+r]! : ZMod q) = 0 := by
    intro i r hi hr
    rw [MlKemRing.intt_interp_kem zeroPoly hz256 MlKemRing.zeroPoly_lt i r hi hr]
    rw [Finset.sum_eq_zero (fun u _ => by rw [MlKemRing.zeroPoly_cast, zero_mul])]
    rw [mul_zero]
  rcases Nat.even_or_odd p with ⟨i, he⟩ | ⟨i, ho⟩
  · have : p = 2*i+0 := by omega
    rw [this]; exact hpair i 0 (by omega) (by norm_num)
  · have : p = 2*i+1 := by omega
    rw [this]; exact hpair i 1 (by omega) (by norm_num)

/-- The K-PKE decryption accumulator, unrolled at `k = paramK = 3` into an explicit `addPoly` chain of the
three fast-NTT products (the `for i in [0:3]` loop). -/
theorem kpkeAcc_fold3 (dkPke c : List UInt8) :
    kpkeAcc dkPke c =
      addPoly (addPoly (addPoly zeroPoly
          (pointwiseNtt (sHatOf dkPke 0) (ntt (uOf c 0))))
          (pointwiseNtt (sHatOf dkPke 1) (ntt (uOf c 1))))
          (pointwiseNtt (sHatOf dkPke 2) (ntt (uOf c 2))) := by
  unfold kpkeAcc sHatOf uOf
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one, bind_pure]
  rfl

/-- **`φ` DISTRIBUTES over the accumulator's `∑ᵢ`** — `φ(intt(∑ᵢ ŝᵢ∘NTT uᵢ)) = ∑ᵢ φ(intt(ŝᵢ∘NTT uᵢ))`,
coefficient-wise in `ℤ_q`, by `intt_addLinear` (§8.2) applied down the three-term `addPoly` chain (all
`addPoly`/`pointwiseNtt` sub-polys are canonical unconditionally). -/
theorem kpkeAcc_intt_cast (dkPke c : List UInt8) (p : Nat) (hp : p < 256) :
    ((intt (kpkeAcc dkPke c))[p]! : ZMod q)
      = ((intt (pointwiseNtt (sHatOf dkPke 0) (ntt (uOf c 0))))[p]! : ZMod q)
      + ((intt (pointwiseNtt (sHatOf dkPke 1) (ntt (uOf c 1))))[p]! : ZMod q)
      + ((intt (pointwiseNtt (sHatOf dkPke 2) (ntt (uOf c 2))))[p]! : ZMod q) := by
  rw [kpkeAcc_fold3]
  set t0 := pointwiseNtt (sHatOf dkPke 0) (ntt (uOf c 0)) with ht0
  set t1 := pointwiseNtt (sHatOf dkPke 1) (ntt (uOf c 1)) with ht1
  set t2 := pointwiseNtt (sHatOf dkPke 2) (ntt (uOf c 2)) with ht2
  have hz256 : (zeroPoly : Poly).size = 256 := by simp [zeroPoly]
  rw [intt_addLinear (addPoly (addPoly zeroPoly t0) t1) t2
        (MlKemRing.addPoly_size _ _) (MlKemRing.addPoly_lt _ _)
        (MlKemRing.pointwiseNtt_size _ _) (MlKemRing.pointwiseNtt_lt _ _) p hp,
      intt_addLinear (addPoly zeroPoly t0) t1
        (MlKemRing.addPoly_size _ _) (MlKemRing.addPoly_lt _ _)
        (MlKemRing.pointwiseNtt_size _ _) (MlKemRing.pointwiseNtt_lt _ _) p hp,
      intt_addLinear zeroPoly t0
        hz256 MlKemRing.zeroPoly_lt
        (MlKemRing.pointwiseNtt_size _ _) (MlKemRing.pointwiseNtt_lt _ _) p hp,
      intt_zeroPoly_cast p hp]
  ring

/-- **THE COEFFICIENT RING-HOM IMAGE OF THE DECRYPTED `w`** — `φ(kpkeW) = φ v − ∑ⱼ φ(sⱼ · uⱼ)` coefficient-wise
in `ℤ_q`, the executable pipeline exhibited in `MlKemCorrect.wVal`'s shape (`v − ∑ⱼ sⱼ·uⱼ`). Assembles all
three §8 reusable legs: `cast_subPoly` (`w = v − NTT⁻¹(acc)`), `kpkeAcc_intt_cast` (`φ∘intt` distributes over
`∑ᵢ` via `intt_addLinear`), and `intt_pointwiseNtt_ntt` (each fast-NTT term is the negacyclic product `sⱼ·uⱼ`,
via `ntt_intt_rightInverse` + `ntt_computes_negacyclic_mul`). Here `sⱼ = intt (sHatOf dkPke j)` and
`uⱼ = uOf c j`; the residual to the LITERAL `MlKemCorrect.wVal` is only the input identification (§8-(2/3/4):
`u = uVec`, `v = vVal`) and lifting `schoolbookMul` into a `CommRing R_q` instance. `hu` — that `u` decodes to
size-256 `R_q` elements — is the byte-codec faithfulness fact (`uOf_size` discharges it). -/
theorem kpkeW_phi (dkPke c : List UInt8) (hu : ∀ i, i < paramK → (uOf c i).size = 256)
    (p : Nat) (hp : p < 256) :
    ((kpkeW dkPke c)[p]! : ZMod q)
      = (((ctDecode c).2[p]! : Nat) : ZMod q)
        - ( ((MlKemRing.schoolbookMul (intt (sHatOf dkPke 0)) (uOf c 0))[p]! : ZMod q)
          + ((MlKemRing.schoolbookMul (intt (sHatOf dkPke 1)) (uOf c 1))[p]! : ZMod q)
          + ((MlKemRing.schoolbookMul (intt (sHatOf dkPke 2)) (uOf c 2))[p]! : ZMod q) ) := by
  have haccsz : (kpkeAcc dkPke c).size = 256 := by rw [kpkeAcc_fold3]; exact MlKemRing.addPoly_size _ _
  have hacclt : ∀ (p : Nat), (kpkeAcc dkPke c)[p]! < q := by
    rw [kpkeAcc_fold3]; exact MlKemRing.addPoly_lt _ _
  have hintt_lt : (intt (kpkeAcc dkPke c))[p]! ≤ q :=
    le_of_lt (intt_lt (kpkeAcc dkPke c) haccsz hacclt p)
  unfold kpkeW
  rw [MlKemRing.cast_subPoly _ _ p hp hintt_lt, kpkeAcc_intt_cast dkPke c p hp,
      intt_pointwiseNtt_ntt (sHatOf dkPke 0) (uOf c 0) (sHatOf_size _ _) (sHatOf_lt _ _)
        (hu 0 (by unfold paramK; omega)),
      intt_pointwiseNtt_ntt (sHatOf dkPke 1) (uOf c 1) (sHatOf_size _ _) (sHatOf_lt _ _)
        (hu 1 (by unfold paramK; omega)),
      intt_pointwiseNtt_ntt (sHatOf dkPke 2) (uOf c 2) (sHatOf_size _ _) (sHatOf_lt _ _)
        (hu 2 (by unfold paramK; omega))]

/-! ### §8.6 — BYTE-CODEC FAITHFULNESS (item 2): the decode legs land canonical `R_q` elements.

The proven codec round-trips live in `MlKemCodecSpec` (`byteDecode₁₂_byteEncode₁₂`, `byteDecode_du/dv_…`)
and `MlKemCodec` (`compress_decompress_id`, over the whole compressed field). Here we discharge the
faithfulness facts the domination assembly (§8.5) consumes: `ŝ` (`sHatOf_size`/`_lt`, above) and `u`
(`uOf_size`, below) decode to genuine size-256 `R_q` ring elements. `v` is the fourth `ctDecode` field. -/

/-- `decompressPoly` unrolled to the indexed-`set!` fold (the loop shape `compressPoly` also has). -/
theorem decompressPoly_fold (d : Nat) (p : Poly) :
    decompressPoly d p =
      List.foldl (fun (out : Poly) (i : Nat) => out.set! i (decompress d p[i]!)) zeroPoly
        (List.range' 0 256 1) := by
  unfold decompressPoly
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

/-- `decompressPoly d p` is a canonical `R_q` element: 256 coefficients. -/
theorem decompressPoly_size (d : Nat) (p : Poly) : (decompressPoly d p).size = 256 := by
  rw [decompressPoly_fold]
  rw [(idxSetFold_spec (fun i => decompress d p[i]!) 256 zeroPoly).1]
  simp [zeroPoly]

/-- The `u`-array `ctDecode` recovers, unrolled at `k = paramK = 3` (three `Decompress_{du} ∘ ByteDecode_{du}`
polynomials). -/
theorem ctDecode_fst (c : List UInt8) :
    (ctDecode c).1 =
      #[decompressPoly du (byteDecodeAt du c.toArray (0 * polyBytes du)),
        decompressPoly du (byteDecodeAt du c.toArray (1 * polyBytes du)),
        decompressPoly du (byteDecodeAt du c.toArray (2 * polyBytes du))] := by
  unfold ctDecode
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

/-- **BYTE-CODEC FAITHFULNESS (u).** Each decoded ciphertext component `uᵢ` (`i < k`) is a canonical size-256
`R_q` ring element — discharging the `hu` hypothesis of `kpkeW_phi`. (`Decompress_{du} ∘ ByteDecode_{du}`
always writes 256 coefficients.) -/
theorem uOf_size (c : List UInt8) (i : Nat) (hi : i < paramK) : (uOf c i).size = 256 := by
  unfold uOf
  rw [ctDecode_fst]
  have : i = 0 ∨ i = 1 ∨ i = 2 := by unfold paramK at hi; omega
  rcases this with h | h | h <;> subst h <;> exact decompressPoly_size _ _

/-- **`φ(kpkeW) = wVal`-SHAPE, with the codec faithfulness DISCHARGED** — `uOf_size` supplies `kpkeW_phi`'s
`hu`, so the executable decrypted `w`'s `ℤ_q` coefficient hom is `φ v − ∑ⱼ φ(sⱼ·uⱼ)` with NO codec-faithfulness
side condition. This is the §8-(1)+(2) result: the coefficient ring hom `φ` carries the byte-exact executable
K-PKE decrypt to the `MlKemCorrect.wVal` algebraic shape over the real negacyclic products `sⱼ·uⱼ`. -/
theorem kpkeW_phi_faithful (dkPke c : List UInt8) (p : Nat) (hp : p < 256) :
    ((kpkeW dkPke c)[p]! : ZMod q)
      = (((ctDecode c).2[p]! : Nat) : ZMod q)
        - ( ((MlKemRing.schoolbookMul (intt (sHatOf dkPke 0)) (uOf c 0))[p]! : ZMod q)
          + ((MlKemRing.schoolbookMul (intt (sHatOf dkPke 1)) (uOf c 1))[p]! : ZMod q)
          + ((MlKemRing.schoolbookMul (intt (sHatOf dkPke 2)) (uOf c 2))[p]! : ZMod q) ) :=
  kpkeW_phi dkPke c (uOf_size c) p hp

/-! ### §8.7 — the REMAINING faithfulness residuals (items 3, 4), each a precise Lean statement.

The §8.5/§8.6 result exhibits `φ(kpkeW) = φ v − ∑ⱼ φ(sⱼ·uⱼ)` — the `wVal` SHAPE over the negacyclic products.
Reaching the LITERAL `MlKemCorrect.mlkem_decrypt_cancellation` (hence `hdom`) additionally requires: a `CommRing`
`R_q` instance carrying `schoolbookMul` as its `*` (so the abstract matrix `sum_comm` cancellation applies), and
the following two SEED-EXPANSION faithfulness facts, stated here precisely against the executable samplers. -/

/-- **ITEM 3 — `ExpandA` faithfulness (NAMED).** The public matrix `Â = expandMatrix ρ` the executable parses
from the seed (`SampleNTT`/XOF) realizes an abstract matrix `A : Fin k → Fin k → Poly` in the sense that each
parsed entry is canonical (size-256, reduced) and matches `A` at every `(i,j)`. Discharging this needs the
`SampleNTT` rejection-sampling faithfulness (uniform `< q` parse from SHAKE-128), which is not built. -/
def ExpandAFaithful (rho : List UInt8) (A : Nat → Nat → Poly) : Prop :=
  ∀ i j, i < paramK → j < paramK →
    ((MlKemSample.expandMatrix rho)[i * paramK + j]!) = A i j
    ∧ (A i j).size = 256 ∧ (∀ (p : Nat), (A i j)[p]! < q)

/-- **ITEM 4 — CBD sampler faithfulness (NAMED).** `samplePolyCBD η B` (centered-binomial from PRF bytes `B`)
realizes the abstract CBD(η) noise polynomial `cbd` that `MlKemDelta` models — each coefficient is the
centered `∑ x - ∑ y` of `2η` PRF bits, canonical in `R_q`. Discharging this needs the `getBit`/`BytesToBits`
faithfulness plus the tie to `MlKemDelta`'s `cbd` law, which is not built. -/
def CbdFaithful (eta : Nat) (bytes : List UInt8) (cbd : Poly) : Prop :=
  MlKemSample.samplePolyCBD eta bytes = cbd ∧ cbd.size = 256 ∧ (∀ (p : Nat), cbd[p]! < q)

/-! ### §8.8 — ITEM (1) DISCHARGED: the `CommRing R_q` carrying `schoolbookMul` as `*`, and the LITERAL
cancellation `toRqKem (kpkeW) = μ + e_total`.

The `CommRing R_q` instance item (1) asks for ALREADY EXISTS as `DecapsCoreSpec.Rq_kem = AdjoinRoot (X²⁵⁶+1)`
(a genuine `CommRing`), and `DecapsCoreSpec.toRqKem_schoolbookMul` proves — for ALL poly pairs — that the coeff
ring hom `toRqKem : Poly → Rq_kem` carries the executable `MlKemRing.schoolbookMul` to the ring `*`. Reusing it
(rather than re-deriving a mirror CommRing on `Array Nat`, which would just re-prove negacyclic-convolution
associativity/distributivity already discharged by `AdjoinRoot`) is the correct assembly. `phiCoeff` (§8.4) is
only ADDITIVE — it does NOT carry `schoolbookMul` (coefficient-wise product ≠ negacyclic convolution) — so the
multiplicative cancellation genuinely needs THIS ring, not `Fin 256 → ℤ_q`.

With that `CommRing`, `MlKemCorrect.mlkem_decrypt_cancellation` (abstract `[CommRing R]`) SPECIALIZES at
`R = Rq_kem`, `k = paramK`. `DecapsCoreSpec.decryptW_eq_spec` already maps the executable decrypted `w` to the
`wVal` SHAPE `toRqKem v − Σⱼ toRqKem sⱼ · toRqKem uⱼ` in `Rq_kem` — and its honest-key hypothesis
(`ŝᵢ = NTT(sᵢ)`) is DISCHARGED here by `ntt_intt_rightInverse` (§8.3): the stored NTT-domain secret
`ŝᵢ = sHatOf` IS `NTT(intt ŝᵢ)`, so `sᵢ := intt ŝᵢ` witnesses it with NO side condition. Composing the two
turns the SHAPE into the LITERAL `μ + e_total`, under the abstract-model identifications of `v, u, s` — which
are exactly items (2)/(3)/(4) + the encrypt-side ring algebra (`EncapsCoreSpec.encrypt_{u,v}_ring_faithful`,
already proved over this same `Rq_kem`). -/

open Dregg2.Crypto.MlKemCodec (dCoeff polyBytes paramK byteDecodeAt ctDecode)

/-- The executable K-PKE decrypt accumulator IS `DecapsCoreSpec.decWFold` (both are the `for i in [0:paramK]`
fold reading `ŝᵢ = ByteDecode₁₂(dk, i·384)`); the do-block unfolds identically. -/
theorem kpkeAcc_eq_decWFold (dkPke c : List UInt8) :
    kpkeAcc dkPke c = DecapsCoreSpec.decWFold dkPke.toArray (ctDecode c).1 := by
  unfold kpkeAcc DecapsCoreSpec.decWFold
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

/-- Bridge the `List.range' 0 paramK 1` fold-sum `DecapsCoreSpec.decryptW_eq_spec` produces to a
`Finset.univ` sum over `Fin paramK` (`paramK = 3`), so it lines up with `MlKemCorrect.wVal`'s `∑ j`. -/
theorem sum_over_paramK {M : Type*} [AddCommMonoid M] (g : Nat → M) :
    ((List.range' 0 paramK 1).map g).sum = ∑ j : Fin paramK, g (j : Nat) := by
  show ((List.range' 0 3 1).map g).sum = ∑ j : Fin 3, g (j : Nat)
  rw [Fin.sum_univ_three]
  rw [show (List.range' 0 3 1) = [0, 1, 2] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fin.val_zero, Fin.val_one,
    Fin.val_two]
  rw [add_zero, add_assoc]

/-- **ITEM (1), the `wVal` SHAPE in the REAL ring `R_q`.** The `toRqKem`-image of the executable decrypted
`w = v − NTT⁻¹(Σᵢ ŝᵢ ∘ NTT(uᵢ))` is `toRqKem v − Σⱼ toRqKem(intt ŝⱼ) · toRqKem uⱼ` over the negacyclic
`CommRing R_q = AdjoinRoot(X²⁵⁶+1)` — the genuine RING product, not the additive-only `phiCoeff`. The stored
NTT-domain secret's honest-key obligation is discharged unconditionally by `ntt_intt_rightInverse`. -/
theorem kpkeW_toRqKem (dkPke c : List UInt8) :
    DecapsCoreSpec.toRqKem (kpkeW dkPke c)
      = DecapsCoreSpec.toRqKem (ctDecode c).2
        - ∑ j : Fin paramK,
            DecapsCoreSpec.toRqKem (intt (sHatOf dkPke j)) * DecapsCoreSpec.toRqKem (uOf c j) := by
  have hkey : ∀ i, i < paramK →
      byteDecodeAt dCoeff dkPke.toArray (i * polyBytes dCoeff) = ntt (intt (sHatOf dkPke i)) :=
    fun i _ => (ntt_intt_rightInverse (sHatOf dkPke i) (sHatOf_size dkPke i) (sHatOf_lt dkPke i)).symm
  have hspec := DecapsCoreSpec.decryptW_eq_spec dkPke c (fun i => intt (sHatOf dkPke i))
    (fun i _ => intt_size (sHatOf dkPke i) (sHatOf_size dkPke i) (sHatOf_lt dkPke i))
    (fun i hi => uOf_size c i hi) hkey
  unfold kpkeW
  rw [kpkeAcc_eq_decWFold, hspec, sum_over_paramK]
  rfl

/-- **ITEM (1) DISCHARGED — the LITERAL `toRqKem (kpkeW) = μ + e_total`.** Given the abstract-model
identifications of the executable's ciphertext ring elements (`sⱼ = toRqKem(intt ŝⱼ)`, `uⱼ = uVec`, `v = vVal`
— the payload of items (2)/(3)/(4) + the encrypt-side algebra, over this SAME `Rq_kem`), the `toRqKem`-image of
the executable decrypted `w` equals `μ + e_total` in `R_q`. This is the ONE step the CommRing enables:
`kpkeW_toRqKem` gives the `wVal` shape over the negacyclic ring product; `MlKemCorrect.mlkem_decrypt_cancellation`
(`Finset.sum_comm` over `[CommRing R]`, here at `R = Rq_kem`) collapses the double matrix sum, exhibiting the
literal `e_total`. -/
theorem kpkeW_toRqKem_cancellation (dkPke c : List UInt8)
    (A : Fin paramK → Fin paramK → DecapsCoreSpec.Rq_kem)
    (s e r e1 du : Fin paramK → DecapsCoreSpec.Rq_kem) (e2 μ dv : DecapsCoreSpec.Rq_kem)
    (hs : ∀ j : Fin paramK, DecapsCoreSpec.toRqKem (intt (sHatOf dkPke j)) = s j)
    (hu : ∀ j : Fin paramK, DecapsCoreSpec.toRqKem (uOf c j) = MlKemCorrect.uVec A r e1 du j)
    (hv : DecapsCoreSpec.toRqKem (ctDecode c).2 = MlKemCorrect.vVal A s e r e2 μ dv) :
    DecapsCoreSpec.toRqKem (kpkeW dkPke c) = μ + MlKemCorrect.eTotal s e r e1 du e2 dv := by
  rw [kpkeW_toRqKem, hv]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hs j, hu j])]
  exact MlKemCorrect.mlkem_decrypt_cancellation A s e r e1 du e2 μ dv

/-- **NON-VACUITY of ITEM (1).** The identification hypotheses of `kpkeW_toRqKem_cancellation` are jointly
SATISFIABLE: the degenerate abstract model `A = 0`, `r = 0`, `s := toRqKem(intt ŝ)`, `e1 := (fun j ↦ toRqKem uⱼ)`,
`du = e2 = dv = 0`, `μ := toRqKem v` makes `uVec = e1 = toRqKem u` and `vVal = μ = toRqKem v`. So item (1) is a
genuine implication, not vacuously true through unsatisfiable hypotheses. -/
theorem kpkeW_toRqKem_cancellation_satisfiable (dkPke c : List UInt8) :
    ∃ (A : Fin paramK → Fin paramK → DecapsCoreSpec.Rq_kem)
      (s e r e1 du : Fin paramK → DecapsCoreSpec.Rq_kem) (e2 μ dv : DecapsCoreSpec.Rq_kem),
      (∀ j : Fin paramK, DecapsCoreSpec.toRqKem (intt (sHatOf dkPke j)) = s j)
      ∧ (∀ j : Fin paramK, DecapsCoreSpec.toRqKem (uOf c j) = MlKemCorrect.uVec A r e1 du j)
      ∧ DecapsCoreSpec.toRqKem (ctDecode c).2 = MlKemCorrect.vVal A s e r e2 μ dv := by
  refine ⟨fun _ _ => 0, fun j => DecapsCoreSpec.toRqKem (intt (sHatOf dkPke j)),
    fun _ => 0, fun _ => 0, fun j => DecapsCoreSpec.toRqKem (uOf c j), fun _ => 0, 0,
    DecapsCoreSpec.toRqKem (ctDecode c).2, 0, fun _ => rfl, ?_, ?_⟩
  · intro j; simp only [MlKemCorrect.uVec, Finset.sum_const_zero, zero_add, zero_mul, add_zero]
  · simp only [MlKemCorrect.vVal, MlKemCorrect.tVec, Finset.sum_const_zero, mul_zero, zero_add,
      add_zero]

/-! ### §8.9 — ITEM (3) closable core: `samplePolyCBD` structural faithfulness + the bit-extraction formula.

`samplePolyCBD η B` writes to `zeroPoly` (size 256) via `set!` a `subQ`-reduced value at each index, so it is
UNCONDITIONALLY a canonical `R_q` element (size 256, every coefficient `< q`) whose `i`-th coefficient is the
FIPS 203 Alg 8 centered `(Σ_{j<η} bit[2iη+j]) − (Σ_{j<η} bit[2iη+η+j])` — the bit-extraction faithfulness,
proved here. The one remaining residual is purely the DISTRIBUTIONAL tie (that this deterministic sampler
realizes the abstract CBD(η) noise `MlKemDelta` models), which lives in the sibling `MlKemDelta` and is not
asserted here. -/

/-- The per-index write of `samplePolyCBD` (its inner `for j in [0:eta]` double accumulator, returning
`subQ x y`), factored out verbatim so the outer `set!`-fold has an opaque value. -/
def cbdVal (eta : Nat) (arr : Array UInt8) (i : Nat) : Nat := Id.run do
  let mut x := 0
  let mut y := 0
  for j in [0:eta] do
    x := x + MlKemSample.getBit arr (2 * i * eta + j)
    y := y + MlKemSample.getBit arr (2 * i * eta + eta + j)
  return MlKemRing.subQ x y

/-- **The bit-extraction faithfulness**: `cbdVal` IS the FIPS 203 Alg 8 centered coefficient
`(Σ_{j<η} bit[2iη+j]) − (Σ_{j<η} bit[2iη+η+j])` reduced into `[0,q)`. The two-accumulator inner `for`-loop is
the pair-fold whose components are the two `Finset.range η` bit-sums (`pairFold_sum`). -/
theorem cbdVal_eq (eta : Nat) (arr : Array UInt8) (i : Nat) :
    cbdVal eta arr i =
      MlKemRing.subQ (∑ j ∈ Finset.range eta, MlKemSample.getBit arr (2 * i * eta + j))
        (∑ j ∈ Finset.range eta, MlKemSample.getBit arr (2 * i * eta + eta + j)) := by
  unfold cbdVal
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  -- the two-`let mut` inner loop desugars (v4.35) to a fold over the `Prod` `Nat × Nat` in
  -- declaration order; each component is a `range η` bit-sum.
  have hpair : ∀ (n : Nat),
      List.foldl (fun (b : Nat × Nat) (a : Nat) =>
          ((b.1 + MlKemSample.getBit arr (2 * i * eta + a),
            b.2 + MlKemSample.getBit arr (2 * i * eta + eta + a)) : Nat × Nat))
          ((0, 0) : Nat × Nat) (List.range' 0 n)
        = ((∑ j ∈ Finset.range n, MlKemSample.getBit arr (2 * i * eta + j),
            ∑ j ∈ Finset.range n, MlKemSample.getBit arr (2 * i * eta + eta + j)) : Nat × Nat) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [List.range'_1_concat, List.foldl_concat, ih, Nat.zero_add, Finset.sum_range_succ,
        Finset.sum_range_succ]
  (rw [hpair eta]) <;> rfl

/-- `samplePolyCBD` unrolled to the indexed-`set!` fold whose per-index write value is `cbdVal`. -/
theorem samplePolyCBD_fold (eta : Nat) (bytes : List UInt8) :
    MlKemSample.samplePolyCBD eta bytes =
      List.foldl (fun (out : Poly) (i : Nat) => out.set! i (cbdVal eta bytes.toArray i)) zeroPoly
        (List.range' 0 256 1) := by
  unfold MlKemSample.samplePolyCBD cbdVal
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

theorem samplePolyCBD_size (eta : Nat) (bytes : List UInt8) :
    (MlKemSample.samplePolyCBD eta bytes).size = 256 := by
  rw [samplePolyCBD_fold, (idxSetFold_spec (fun i => cbdVal eta bytes.toArray i) 256 zeroPoly).1]
  simp [zeroPoly]

/-- **The CBD coefficient, byte-faithful.** Coefficient `j` of `samplePolyCBD η B` is exactly the FIPS 203
Alg 8 centered bit-difference `subQ (Σ bit) (Σ bit)` — the bit-extraction faithfulness at every index. -/
theorem samplePolyCBD_getElem (eta : Nat) (bytes : List UInt8) (j : Nat) (hj : j < 256) :
    (MlKemSample.samplePolyCBD eta bytes)[j]!
      = MlKemRing.subQ (∑ i ∈ Finset.range eta, MlKemSample.getBit bytes.toArray (2 * j * eta + i))
          (∑ i ∈ Finset.range eta, MlKemSample.getBit bytes.toArray (2 * j * eta + eta + i)) := by
  rw [samplePolyCBD_fold,
    (idxSetFold_spec (fun i => cbdVal eta bytes.toArray i) 256 zeroPoly).2 j hj
      (by simp [zeroPoly]; omega),
    cbdVal_eq]

theorem samplePolyCBD_lt (eta : Nat) (bytes : List UInt8) : ∀ (p : Nat),
    (MlKemSample.samplePolyCBD eta bytes)[p]! < q := by
  intro p
  by_cases hp : p < 256
  · rw [samplePolyCBD_getElem eta bytes p hp]; exact MlKemRing.subQ_lt _ _
  · rw [MlKemRing.getElem!_ge _ p (by rw [samplePolyCBD_size]; omega)]; unfold MlKemRing.q; omega

/-- **`CbdFaithful` is INHABITED** — the CBD sampler's own output is a canonical `R_q` element realized by
`samplePolyCBD` (reflexively), with the size + reduced + bit-extraction structural faithfulness proved. The
distributional tie to `MlKemDelta`'s CBD law is the sole remaining (sibling-owned) residual. -/
theorem cbdFaithful_self (eta : Nat) (bytes : List UInt8) :
    CbdFaithful eta bytes (MlKemSample.samplePolyCBD eta bytes) :=
  ⟨rfl, samplePolyCBD_size eta bytes, samplePolyCBD_lt eta bytes⟩

/-! ### §8.10 — ITEM 3 DISCHARGED: `ExpandA` faithfulness via the REJECTION-FILL invariant.

`SampleNTT` (FIPS 203 Alg 7) fills exactly 256 coefficients by a 12-bit parse-and-reject loop over SHAKE-128:
each 3-byte read yields two candidates `d1, d2`, and each is APPENDED iff `< q` (else dropped), stopping at 256.
Its `forIn` is BRANCHING (a conditional double-push), so it does not reduce to a clean `foldl` of a total
step. The content here is the **fill invariant**: the branching loop's accumulator holds exactly the `< q`-
accepted candidates in order, truncated at 256 — i.e. `SampleNTT` equals the DECLARATIVE `filter (· < q)` then
`take 256` of the parsed candidate stream (`sampleNTT_spec`). The abstract matrix `A` uses the SAME reject rule,
so faithfulness is that the executable accept-sequence equals the declarative one (NOT `SampleNTT = SampleNTT`,
which would be vacuous — `abstractA` is the filter/take spec, not the sampler). `< q` (every coefficient) is
UNCONDITIONAL; the "exactly 256" fill needs a long-enough stream, carried as the clean named hypothesis
`hlen` (the deployed `rejReads = 512`-read SHAKE-128 stream yields `≥ 256` accepts — the `expandMatrix_shape`
gate witnesses it concretely for `ρ = [0,…,31]`). -/

section ExpandAFill
open Dregg2.Crypto.MlKemSample (sampleNTT expandMatrix rejReads)
open Dregg2.Crypto.Keccak (shake128)

/-- `foldl` congruence under a pointwise-equal step (local, to avoid a cross-module open). -/
theorem rejFoldlExt {A B : Type} (f g : B → A → B) (h : ∀ b a, f b a = g b a)
    (l : List A) (init : B) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [h init hd]; exact ih _

/-- Single-candidate rejection push: append `d` iff there's room (`< 256`) and it passes (`< q`). -/
def pushIf (acc : Array Nat) (d : Nat) : Array Nat :=
  if acc.size < 256 then (if d < q then acc.push d else acc) else acc

/-- The SHAKE-128 byte stream `sampleNTT` reads (`3·rejReads` bytes). -/
def streamOf (seed : List UInt8) : Array UInt8 := (shake128 seed (3 * rejReads)).toArray

/-- The two 12-bit candidates parsed from read `r` of `stream` (`d1 = b0 + 256·(b1 mod 16)`,
`d2 = ⌊b1/16⌋ + 16·b2`). -/
def candsOfRead (stream : Array UInt8) (r : Nat) : List Nat :=
  [ stream[3*r]!.toNat + 256 * (stream[3*r+1]!.toNat % 16),
    stream[3*r+1]!.toNat / 16 + 16 * stream[3*r+2]!.toNat ]

/-- The full flattened candidate list of `sampleNTT seed`: `d1,d2` for each of the `rejReads` reads. -/
def allCands (seed : List UInt8) : List Nat :=
  (List.range' 0 rejReads 1).flatMap (candsOfRead (streamOf seed))

/-- One read of `sampleNTT`: two conditional pushes (the branching `forIn` body). -/
def rejStep (seed : List UInt8) (acc : Array Nat) (r : Nat) : Array Nat :=
  pushIf (pushIf acc ((streamOf seed)[3*r]!.toNat + 256 * ((streamOf seed)[3*r+1]!.toNat % 16)))
         ((streamOf seed)[3*r+1]!.toNat / 16 + 16 * (streamOf seed)[3*r+2]!.toNat)

/-- Seed for matrix entry `(i,j)`: `ρ ‖ IntegerToBytes(j,1) ‖ IntegerToBytes(i,1)` (FIPS 203 Alg 13). -/
def seedOf (rho : List UInt8) (i j : Nat) : List UInt8 := rho ++ [UInt8.ofNat j, UInt8.ofNat i]

/-- **The DECLARATIVE abstract matrix.** Entry `(i,j)` is the first 256 `< q`-accepted 12-bit candidates of the
SHAKE-128 stream over `ρ ‖ j ‖ i` — the FIPS 203 rejection rule stated declaratively (`filter`/`take`), NOT the
executable sampler. This is what makes `ExpandAFaithful` non-vacuous. -/
def abstractA (rho : List UInt8) (i j : Nat) : Poly :=
  (((allCands (seedOf rho i j)).filter (· < q)).take 256).toArray

/-- The branching `sampleNTT` `forIn` reduces to a `foldl` of `rejStep` (the conditional-double-push step). -/
theorem sampleNTT_foldl (seed : List UInt8) :
    sampleNTT seed = (List.range' 0 rejReads 1).foldl (rejStep seed) #[] := by
  unfold MlKemSample.sampleNTT rejStep streamOf
  -- Abstract the (large) SHAKE-128 stream so the branching body is SMALL — keeps the simp/rfl cheap.
  generalize (shake128 seed (3 * rejReads)).toArray = S
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    ← apply_ite, List.forIn_pure_yield_eq_foldl, bind_pure, Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
  refine rejFoldlExt _ _ ?_ _ _
  intro b a
  simp only [pushIf]
  split_ifs <;> rfl

/-- The double-push per read is `pushIf` over the flattened candidate stream. -/
theorem foldl_rejStep_flatMap (seed : List UInt8) (L : List Nat) (init : Array Nat) :
    L.foldl (rejStep seed) init
      = (L.flatMap (candsOfRead (streamOf seed))).foldl pushIf init := by
  induction L generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.flatMap_cons, List.foldl_append, candsOfRead]
    rw [ih]; rfl

/-- **THE REJECTION-FILL INVARIANT.** Folding `pushIf` over a candidate list `cs` from any accumulator whose
length is `≤ 256` yields exactly the `< q`-accepted candidates, appended and truncated at 256 — the declarative
characterization of the branching accept/reject loop (the accept branch appends the `< q` value; the reject
branch and the full accumulator are no-ops). -/
theorem pushIf_foldl_spec (cs : List Nat) (init : Array Nat) (hinit : init.size ≤ 256) :
    (cs.foldl pushIf init).toList = (init.toList ++ cs.filter (· < q)).take 256 := by
  induction cs generalizing init with
  | nil =>
    simp only [List.filter_nil, List.append_nil, List.foldl_nil]
    rw [List.take_of_length_le]; rwa [Array.length_toList]
  | cons d rest ih =>
    simp only [List.foldl_cons]
    have hstep : (pushIf init d).size ≤ 256 := by
      unfold pushIf; split_ifs with h1 h2
      · rw [Array.size_push]; omega
      · exact hinit
      · exact hinit
    rw [ih (pushIf init d) hstep]
    by_cases hd : d < q
    · rw [List.filter_cons_of_pos (by simpa using hd)]
      by_cases hsz : init.size < 256
      · have hpu : pushIf init d = init.push d := by unfold pushIf; rw [if_pos hsz, if_pos hd]
        rw [hpu, Array.toList_push]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      · have h256 : init.toList.length = 256 := by rw [Array.length_toList]; omega
        have hpu : pushIf init d = init := by unfold pushIf; rw [if_neg hsz]
        rw [hpu, List.take_append_of_le_length (by omega),
            List.take_append_of_le_length (by omega)]
    · rw [List.filter_cons_of_neg (by simpa using hd)]
      have hpu : pushIf init d = init := by
        unfold pushIf
        by_cases h1 : init.size < 256
        · rw [if_pos h1, if_neg hd]
        · rw [if_neg h1]
      rw [hpu]

/-- **The declarative rejection-sample spec** — `sampleNTT` is exactly the first 256 of the `< q`-accepted
12-bit candidates parsed from the SHAKE-128 stream (the fill invariant, assembled). -/
theorem sampleNTT_spec (seed : List UInt8) :
    sampleNTT seed = (((allCands seed).filter (· < q)).take 256).toArray := by
  rw [sampleNTT_foldl, foldl_rejStep_flatMap]
  show List.foldl pushIf #[] (allCands seed) = _
  have key : (List.foldl pushIf #[] (allCands seed)).toList
      = ((allCands seed).filter (· < q)).take 256 := by
    have h := pushIf_foldl_spec (allCands seed) #[] (by simp)
    simpa using h
  conv_lhs => rw [← Array.toArray_toList (xs := List.foldl pushIf #[] (allCands seed))]
  rw [key]

/-- Every coefficient of `sampleNTT seed` is `< q` — UNCONDITIONAL (each accepted candidate passed the test). -/
theorem sampleNTT_lt (seed : List UInt8) (p : Nat) : (sampleNTT seed)[p]! < q := by
  rw [sampleNTT_spec, List.getElem!_toArray]
  by_cases hp : p < (((allCands seed).filter (· < q)).take 256).length
  · have hmemf := List.mem_of_mem_take (List.getElem_mem hp)
    have hlt := (List.mem_filter.mp hmemf).2
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hp]
    simpa using hlt
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide

/-- `sampleNTT seed` has exactly 256 coefficients WHEN the stream yields ≥ 256 accepts (the deployed
SHAKE-128 stream is long enough — carried as a clean named hypothesis, not a fake). -/
theorem sampleNTT_size (seed : List UInt8)
    (hlen : 256 ≤ ((allCands seed).filter (· < q)).length) :
    (sampleNTT seed).size = 256 := by
  rw [sampleNTT_spec, List.size_toArray, List.length_take, Nat.min_eq_left hlen]

/-- `expandMatrix ρ` unrolled at `k = 3` to the explicit `3×3` array of `sampleNTT` entries. -/
theorem expandMatrix_unroll (rho : List UInt8) :
    expandMatrix rho =
      #[ sampleNTT (seedOf rho 0 0), sampleNTT (seedOf rho 0 1), sampleNTT (seedOf rho 0 2),
         sampleNTT (seedOf rho 1 0), sampleNTT (seedOf rho 1 1), sampleNTT (seedOf rho 1 2),
         sampleNTT (seedOf rho 2 0), sampleNTT (seedOf rho 2 1), sampleNTT (seedOf rho 2 2) ] := by
  unfold MlKemSample.expandMatrix seedOf
  simp only [MlKemSample.k, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_one_sub_one, Nat.div_one]
  rfl

/-- **ITEM 3 DISCHARGED — `ExpandAFaithful` is INHABITED by the declarative rejection-sample matrix.** Under the
long-enough-stream hypothesis `hlen` (per entry), the executable `expandMatrix ρ` at every `(i,j)` IS the
abstract `abstractA ρ`, which is canonical (256 coefficients, all `< q`). Non-vacuous: `abstractA` is the
`filter (· < q)`/`take 256` DECLARATIVE spec, and `sampleNTT_spec` (the fill invariant) is what bridges the
executable branching loop to it. -/
theorem expandAFaithful (rho : List UInt8)
    (hlen : ∀ i j, i < paramK → j < paramK →
       256 ≤ ((allCands (seedOf rho i j)).filter (· < q)).length) :
    ExpandAFaithful rho (abstractA rho) := by
  intro i j hi hj
  have hi3 : i < 3 := hi
  have hj3 : j < 3 := hj
  have hbridge : abstractA rho i j = sampleNTT (seedOf rho i j) := by
    unfold abstractA; exact (sampleNTT_spec _).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [expandMatrix_unroll, hbridge]
    -- SYMBOLIC index reduction (no kernel `rfl` over the sampler terms — that would deep-reduce SHAKE).
    interval_cases i <;> interval_cases j <;>
      simp only [paramK, Nat.reduceMul, Nat.reduceAdd, List.getElem!_toArray,
        List.getElem!_cons_succ, List.getElem!_cons_zero]
  · rw [hbridge]; exact sampleNTT_size _ (hlen i j hi hj)
  · intro p; rw [hbridge]; exact sampleNTT_lt _ p

end ExpandAFill

/-! ## AXIOM HYGIENE — every ∀-theorem is kernel-clean (⊆ {propext, Classical.choice, Quot.sound}).
`realDk_good` / `ekOfDk_realDk` / `emptyDk_not_good` / `roundtrip_fails_le_delta_nonvacuous` (the concrete byte
checks) are NOT in this list: they carry the `native_decide` residual, and NOTHING above depends on them. -/

#assert_all_clean [
  byteEncode₁_byteDecode₁,
  compressPoly_getElem,
  compress_w_eq_msgPoly,
  kpkeDecrypt_recovers,
  mlkem_roundtrip_of_kpke,
  fullKemApi_fips203,
  fullKemApi_x25519,
  fullKemApi_agrees,
  winProb_mono,
  roundtrip_fails_le_delta,
  roundtrip_fails_le_delta_2pow140,
  intt_size,
  intt_lt,
  intt_addLinear_pair,
  intt_addLinear,
  inttC_nttC,
  ntt_intt_rightInverse,
  phiCoeff_addPoly,
  sHatOf_size,
  sHatOf_lt,
  intt_pointwiseNtt_ntt,
  intt_zeroPoly_cast,
  kpkeAcc_fold3,
  kpkeAcc_intt_cast,
  kpkeW_phi,
  decompressPoly_fold,
  decompressPoly_size,
  ctDecode_fst,
  uOf_size,
  kpkeW_phi_faithful,
  kpkeAcc_eq_decWFold,
  sum_over_paramK,
  kpkeW_toRqKem,
  kpkeW_toRqKem_cancellation,
  kpkeW_toRqKem_cancellation_satisfiable,
  cbdVal_eq,
  samplePolyCBD_fold,
  samplePolyCBD_size,
  samplePolyCBD_getElem,
  samplePolyCBD_lt,
  cbdFaithful_self,
  sampleNTT_foldl,
  foldl_rejStep_flatMap,
  pushIf_foldl_spec,
  sampleNTT_spec,
  sampleNTT_lt,
  sampleNTT_size,
  expandMatrix_unroll,
  expandAFaithful
]

end Dregg2.Crypto.MlKemFips203FullDim
