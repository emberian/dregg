/-
# `Dregg2.Crypto.MlDsaKeygenRefine` — the BYTE↔RING ML-DSA-65 KeyGen refinement, ∀ (proven).

`MlDsaKeygen` states the OPEN obligation: decoding the byte-level `pk`/`sk` that `mldsaKeygenInternal`
emits recovers EXACTLY the ring-level `(ρ, K, s1, s2, t1, t0)` that the abstract `mldsaKeygenRing`
computes. This module DISCHARGES it — a genuine `∀`-refinement whose specification side is the RING
generator (`ExpandA` / `ExpandS` / `NTT` / matvec / `Power2Round`, FIPS 204 Alg 6 steps 1–5), NOT the byte
implementation restated. It is the ML-DSA mirror of `MlKemKeygenRefine.kpkeKeyGen_refines_ring`.

It rides:

* the codec round-trip `VerifyCoreEqSpec.unpackBits_packBits` (`unpackBits ∘ packBits = id` for size-256
  coefficient arrays whose entries are below `2^cbits`), lifted to the two ML-DSA public-key /
  secret-key layouts by `CodecRoundTrip.pkDecode_pkEncode` (`pk`) and `skDecode_skEncode` (`sk`, §7),
* the `BitPack` SIGN map inverse `bDecode_bEncode` (§2): `b − s` packing round-trips on the whole
  codomain `c ≤ b ∨ q − m ≤ c < q`, and the packed field stays `≤ b + m` (so it fits `2^cbits`),
* the per-coefficient BOUNDS, PROVED over the `Id.run do` loops (§4–§6):
  `Power2Round` ⇒ `t1[i][j] < 2¹⁰` and `t0[i][j] ∈ [0,2¹²] ∪ (q−2¹², q)` (§3, `power2round_t1_lt` /
  `power2round_t0_range`, unconditional in the input coefficient), `ExpandS` ⇒ every `s1`/`s2`
  coefficient lies in `[0,η] ∪ [q−η, q)` (§5, a `forIn` invariant through the `RejBoundedPoly`
  rejection loop), plus the vector shapes `|t1| = |t0| = k`, `|s1| = ℓ`, `|s2| = k` (§6),
* the FIPS 202 fixed-output-length fact for SHAKE-256 (§1): `|ρ| = |K| = 32`, `|tr| = 64`.

## WHAT IS UNCONDITIONAL, AND THE ONE NAMED LEG

The `pk` half — `mldsaKeygen_pk_refines_ring` (§9) — is UNCONDITIONAL: `∀ ξ`, no hypothesis at all.

The `sk` half carries exactly ONE named hypothesis. `RejBoundedPoly` (FIPS 204 Alg 31) samples 256
coefficients by REJECTION from a FIXED 512-byte SHAKE-256 prefix. That it collects all 256 within the
budget is a property OF THE XOF OUTPUT, not a theorem: an adversarial stream of all-`0xF` nibbles would
yield fewer, and the emitted `sk` would then pack short blocks. So the `s1`/`s2` SHAPE is carried as the
EXPLICIT hypothesis `ExpandSSized` (§12) — NOT a `sorry`, NOT an axiom — exactly as `MlKemKeygenRefine`
carried its `ρ`-length side condition before discharging it. `expandS_sized_witness` (§14) shows it is NOT
vacuous: it HOLDS, by `native_decide`, on a concrete seed. Every OTHER leg (the codomains, the block
layout, the codec inversion, the `|ρ|=|K|=32` / `|tr|=64` lengths) is proved outright.

## A NOTE ON `tLoop`

`MlDsaKeygen.tLoop` is built from a ONE-mutable `tPairs` (an `Array (Poly × Poly)` push-fold) rather than
two parallel `mut` vectors. Same values, same order — but a two-`mut` `do`-loop elaborates to a `forIn`
over an `MProd` state whose `List.foldl` normalisation the KERNEL cannot check here: every iteration
carries the term `p2rLoop (addPoly (intt (matAcc …)) …)`, and verifying that rewrite delta-unfolds
`intt`/`matAcc`/`p2rLoop` symbolically (256-point loops over symbolic arrays) until it deep-recurses (>40G,
OOM). The single-`mut` `out.push (f i)` shape normalises to a plain indexed push-fold whose spec applies by
UNIFICATION, leaving `f` abstract — the shape the ML-KEM ring keygen already uses. The NIST ACVP KATs in
`MlDsaKeygenAcvp` still pass byte-for-byte, which is the check that the restructure is output-preserving.

No `sorry`, no user `axiom`; the ∀-theorems are `#assert_axioms`-clean. §14 prints the axiom sets.
Public references: NIST FIPS 202 (SHA-3/SHAKE), FIPS 204 (ML-DSA) §5.1, §7.1–§7.2, Algorithms 6, 22–25,
31, 33, 35.
-/
import Dregg2.Crypto.MlDsaKeygen
import Dregg2.Crypto.CodecRoundTrip
import Dregg2.Tactics
import Mathlib

namespace Dregg2.Crypto.MlDsaKeygenRefine

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly ntt intt pointwiseMul addPoly getElem!_ge)
open Dregg2.Crypto.MlDsaExpandA (expandA)
open Dregg2.Crypto.MlDsaCodec (paramK paramL t1Bits t1PolyBytes pkEncode pkDecode packBits unpackBits)
open Dregg2.Crypto.MlDsaKeygen (etaP etaBits t0Half t0Bits twoD sReads coeffFromHalfByte rejBoundedPoly tPairs
  expandS power2round bEncode packEta packT0 RingKey matAcc p2rLoop s1HatOf tLoop mldsaKeygenRing
  skEncode mldsaKeygenInternal)
open Dregg2.Crypto.Keccak (shake256 squeeze keccakF)
open Dregg2.Crypto.CodecRoundTrip (getElem!_append_left getElem!_append_right getElem!_extract
  appendFold_spec pushIdxFold_spec unpackBits_eq_of_window pkDecode_pkEncode)
open Dregg2.Crypto.VerifyCoreEqSpec (arrayExtAll size_mkEmpty packBits_size unpackBits_size
  unpackBits_packBits getElem!_push_lt getElem!_push_eq)

set_option maxRecDepth 8000

/-! ## §0 — small array / fold bookkeeping. -/

/-- `Array.map` at an in-range index. -/
theorem getElem!_map {β γ} [Inhabited β] [Inhabited γ] (f : β → γ) (a : Array β) (j : Nat)
    (hj : j < a.size) : (a.map f)[j]! = f (a[j]!) := by
  have hj' : j < (a.map f).size := by rw [Array.size_map]; exact hj
  rw [getElem!_pos _ j hj', getElem!_pos a j hj, Array.getElem_map]

/-- Two `map`s that cancel pointwise on the (in-range) entries cancel outright. -/
theorem map_map_cancel (p : Array Nat) (F G : Nat → Nat)
    (h : ∀ j, j < p.size → G (F (p[j]!)) = p[j]!) : (p.map F).map G = p := by
  apply arrayExtAll
  · rw [Array.size_map, Array.size_map]
  · intro j hj
    rw [Array.size_map, Array.size_map] at hj
    rw [getElem!_map _ _ j (by rw [Array.size_map]; exact hj), getElem!_map _ _ j hj, h j hj]

/-- The zero polynomial has 256 slots. -/
theorem zeroPoly_size : zeroPoly.size = 256 := by
  simp [Dregg2.Crypto.MlDsaRing.zeroPoly]

/-- Every slot of the zero polynomial reads `0`. -/
theorem zeroPoly_get (j : Nat) : zeroPoly[j]! = 0 := by
  by_cases h : j < 256
  · rw [getElem!_pos _ j (by rw [zeroPoly_size]; exact h)]
    simp [Dregg2.Crypto.MlDsaRing.zeroPoly]
  · exact getElem!_ge _ j (by rw [zeroPoly_size]; omega)

/-- A `List`-append fold, transported to an `Array`-append fold (`toArray` is a monoid map). -/
theorem listAppendFold_toArray (g : Nat → List UInt8) :
    ∀ (n : Nat) (init : List UInt8),
      (List.foldl (fun dk i => dk ++ g i) init (List.range' 0 n 1)).toArray =
        List.foldl (fun out i => out ++ (g i).toArray) init.toArray (List.range' 0 n 1) := by
  intro n
  induction n with
  | zero => intro init; simp
  | succ k ih =>
    intro init
    simp only [List.range'_1_concat, List.foldl_concat, ← List.append_toArray, ih]

/-- Indexed `set!`-fold on a PAIR of arrays (the `MProd` accumulator the two-`mut` `do`-loops build). -/
theorem setIdxFold2_spec {β γ} [Inhabited β] [Inhabited γ] (g : Nat → β) (h : Nat → γ)
    (b0 : Array β) (c0 : Array γ) :
    ∀ (n : Nat),
      let r := List.foldl (fun (p : MProd (Array β) (Array γ)) j => ⟨p.1.set! j (g j), p.2.set! j (h j)⟩)
        (⟨b0, c0⟩ : MProd (Array β) (Array γ)) (List.range' 0 n 1)
      r.1.size = b0.size ∧ r.2.size = c0.size
      ∧ (∀ j, j < n → j < b0.size → r.1[j]! = g j)
      ∧ (∀ j, j < n → j < c0.size → r.2[j]! = h j) := by
  intro n
  induction n with
  | zero => refine ⟨rfl, rfl, by intro j hj; omega, by intro j hj; omega⟩
  | succ k ih =>
    obtain ⟨hsz1, hsz2, hlo1, hlo2⟩ := ih
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    set P := List.foldl (fun (p : MProd (Array β) (Array γ)) j => ⟨p.1.set! j (g j), p.2.set! j (h j)⟩)
      (⟨b0, c0⟩ : MProd (Array β) (Array γ)) (List.range' 0 k 1) with hP
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (P.1.set! k (g k)).size = _
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz1]
    · show (P.2.set! k (h k)).size = _
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz2]
    · intro j hj hjb
      show (P.1.set! k (g k))[j]! = g j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · rw [Dregg2.Crypto.CodecRoundTrip.getElem!_set!_ne _ _ _ _ (by omega), hlo1 j hlt hjb]
      · subst heq
        rw [Dregg2.Crypto.CodecRoundTrip.getElem!_set!_self _ _ _ (by rw [hsz1]; exact hjb)]
    · intro j hj hjb
      show (P.2.set! k (h k))[j]! = h j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · rw [Dregg2.Crypto.CodecRoundTrip.getElem!_set!_ne _ _ _ _ (by omega), hlo2 j hlt hjb]
      · subst heq
        rw [Dregg2.Crypto.CodecRoundTrip.getElem!_set!_self _ _ _ (by rw [hsz2]; exact hjb)]

/-- Indexed `push`-fold on a PAIR of arrays (the two-`mut` accumulate loops). -/
theorem pushIdxFold2_spec {β γ} [Inhabited β] [Inhabited γ] (g : Nat → β) (h : Nat → γ)
    (b0 : Array β) (c0 : Array γ) :
    ∀ (n : Nat),
      let r := List.foldl (fun (p : MProd (Array β) (Array γ)) j => ⟨p.1.push (g j), p.2.push (h j)⟩)
        (⟨b0, c0⟩ : MProd (Array β) (Array γ)) (List.range' 0 n 1)
      r.1.size = b0.size + n ∧ r.2.size = c0.size + n
      ∧ (∀ j, j < n → r.1[b0.size + j]! = g j) ∧ (∀ j, j < n → r.2[c0.size + j]! = h j) := by
  intro n
  induction n with
  | zero => refine ⟨rfl, rfl, by intro j hj; omega, by intro j hj; omega⟩
  | succ k ih =>
    obtain ⟨hsz1, hsz2, hlo1, hlo2⟩ := ih
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    set P := List.foldl (fun (p : MProd (Array β) (Array γ)) j => ⟨p.1.push (g j), p.2.push (h j)⟩)
      (⟨b0, c0⟩ : MProd (Array β) (Array γ)) (List.range' 0 k 1) with hP
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (P.1.push (g k)).size = _
      rw [Array.size_push, hsz1]; omega
    · show (P.2.push (h k)).size = _
      rw [Array.size_push, hsz2]; omega
    · intro j hj
      show (P.1.push (g k))[b0.size + j]! = g j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · rw [getElem!_push_lt _ _ _ (by rw [hsz1]; omega), hlo1 j hlt]
      · subst heq
        rw [show b0.size + j = P.1.size from by rw [hsz1], getElem!_push_eq]
    · intro j hj
      show (P.2.push (h k))[c0.size + j]! = h j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · rw [getElem!_push_lt _ _ _ (by rw [hsz2]; omega), hlo2 j hlt]
      · subst heq
        rw [show c0.size + j = P.2.size from by rw [hsz2], getElem!_push_eq]

/-! ## §1 — the FIPS 202 squeeze-length fact: `|SHAKE-256(·, n)| = n`, ∀.

`ρ`, `K` and `tr` have their FIPS lengths only because SHAKE-256 really emits what it is asked for. That
is a `∀`-fact about `Keccak.squeeze`, proved here from its definition — no KAT, no hypothesis. The route
mirrors `MlKemKeygenRefine`'s §0 (same `Keccak.squeeze`, same two-mutable-variable `forIn` obstruction);
it is repeated here rather than imported so this module does not depend on the ML-KEM refinement file.
Public reference: FIPS 202 §4 (sponge), §6.3 (SHAKE-256). -/

/-- **The generic `Id`-monad `forIn` measure induction.** If every iteration is a `yield` of a pure step
`g` that grows the `ℕ`-measure `sz` by exactly `k`, the whole loop grows `sz` by `l.length * k` — the step
may branch internally, only the measure step must be uniform. -/
theorem forIn_id_measure {σ : Type} (sz : σ → Nat) (k : Nat)
    (f : Nat → σ → Id (ForInStep σ)) (g : Nat → σ → σ)
    (hf : ∀ i s, f i s = pure (ForInStep.yield (g i s)))
    (hsz : ∀ i s, sz (g i s) = sz s + k) :
    ∀ (l : List Nat) (init : σ), sz (forIn l init f : Id σ) = sz init + l.length * k := by
  intro l
  induction l with
  | nil => intro init; show sz init = sz init + 0 * k; simp
  | cons a t ih =>
    intro init
    rw [List.forIn_cons]
    simp only [hf]
    show sz (forIn t (g a init) f : Id σ) = _
    rw [ih (g a init), hsz]
    simp [Nat.succ_mul]
    ring

/-- Ceiling division delivers at least the numerator. -/
theorem ceilDiv_mul_ge (rate outLen : Nat) (hr : 0 < rate) :
    outLen ≤ ((outLen + rate - 1) / rate) * rate := by
  have h1 := Nat.div_add_mod (outLen + rate - 1) rate
  have h2 : (outLen + rate - 1) % rate < rate := Nat.mod_lt _ hr
  have h3 : outLen ≤ rate * ((outLen + rate - 1) / rate) := by omega
  calc outLen ≤ rate * ((outLen + rate - 1) / rate) := h3
    _ = ((outLen + rate - 1) / rate) * rate := Nat.mul_comm _ _

/-- `f <$> x = f x` in `Id`. -/
theorem id_map_apply {α β : Type} (f : α → β) (x : Id α) : (f <$> x : Id β) = f x := rfl

/-- **THE FIPS 202 SQUEEZE-LENGTH THEOREM, ∀.** For every positive rate, sponge state and requested
length, `Keccak.squeeze` returns EXACTLY `outLen` bytes. -/
theorem squeeze_length (rate : Nat) (hr : 0 < rate) (s0 : Array UInt64) (outLen : Nat) :
    (squeeze rate s0 outLen).length = outLen := by
  unfold squeeze
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl]
  have hkey := forIn_id_measure (σ := Array UInt64 × Array UInt8) (fun r => r.2.size) rate
      (fun blk __s => (do
        let __s_1 ← pure (List.foldl
          (fun b a => b.push (__s.1[a / 8]! >>> (8 * (a % 8)).toUInt64).toUInt8) __s.2 (List.range' 0 rate))
        if blk + 1 < (outLen + rate - 1) / rate then pure (ForInStep.yield (keccakF __s.1, __s_1))
          else pure (ForInStep.yield (__s.1, __s_1))))
      (fun blk r => (if blk + 1 < (outLen + rate - 1) / rate then keccakF r.1 else r.1,
        List.foldl
          (fun b a => b.push (r.1[a / 8]! >>> (8 * (a % 8)).toUInt64).toUInt8) r.2 (List.range' 0 rate)))
      (by intro i s; by_cases h : i + 1 < (outLen + rate - 1) / rate <;> simp [h])
      (by intro i s; simp)
      (List.range' 0 ((outLen + rate - 1) / rate)) (s0, #[])
  simp only [List.length_range', Array.size_empty, Nat.zero_add] at hkey
  rw [id_map_apply]
  simp only [List.length_take, Array.length_toList]
  exact Nat.min_eq_left (le_of_le_of_eq (ceilDiv_mul_ge rate outLen hr) hkey.symm)

/-- **`SHAKE-256` emits exactly `outLen` bytes, ∀ input.** (FIPS 202: rate `1600 − 2·256 = 1088` bits
`= 136` bytes.) -/
theorem shake256_length (input : List UInt8) (outLen : Nat) :
    (shake256 input outLen).length = outLen := by
  unfold Dregg2.Crypto.Keccak.shake256
  exact squeeze_length 136 (by norm_num) _ outLen

/-! ## §2 — the `BitPack` sign map and its inverse.

FIPS 204 `BitPack(w, a, b)` stores the field `b − wⱼ`; `BitUnpack(v, a, b)` reads `b − vⱼ` back. On the
canonical-`ℤ_q` representation the encode is `MlDsaKeygen.bEncode b c = (b + q − c) mod q` and the decode
is `bDecode` below. They are mutually inverse on the codomain `c ≤ b ∨ q − m ≤ c < q` (`m ≤ b` the
negative-wing radius), and the packed field never exceeds `b + m` — which is what makes it fit in
`bitlen(2b)` bits. -/

/-- **`BitPack` sign map (DECODE)** — the inverse of `MlDsaKeygen.bEncode`. A field `f` decodes to the
signed value `b − f`, carried as its canonical `ℤ_q` rep. Covers `s1`/`s2` (`b = η`) and `t0`
(`b = 2^{d−1}`). -/
def bDecode (b f : Nat) : Nat := if f ≤ b then b - f else q - (f - b)

/-- **The sign map round-trips**: `bDecode b (bEncode b c) = c` for every canonical-`ℤ_q` coefficient in
the `BitPack` codomain (`c ≤ b`, or the negative wing `q − m ≤ c < q` of radius `m ≤ b`). -/
theorem bDecode_bEncode (b m c : Nat) (hm : m ≤ b) (hbm : b + m < q)
    (hc : c ≤ b ∨ (q - m ≤ c ∧ c < q)) : bDecode b (bEncode b c) = c := by
  have hq : q = 8380417 := rfl
  unfold bDecode Dregg2.Crypto.MlDsaKeygen.bEncode
  rw [hq] at hbm hc ⊢
  rcases hc with h | ⟨h1, h2⟩ <;> split_ifs <;> omega

/-- **The packed field is small**: `bEncode b c ≤ b + m` on the same codomain. With `2^cbits > b + m`
this is what lets `packBits`/`unpackBits` round-trip the field layer. -/
theorem bEncode_le (b m c : Nat) (hm : m ≤ b) (hbm : b + m < q)
    (hc : c ≤ b ∨ (q - m ≤ c ∧ c < q)) : bEncode b c ≤ b + m := by
  have hq : q = 8380417 := rfl
  unfold Dregg2.Crypto.MlDsaKeygen.bEncode
  rw [hq] at hbm hc ⊢
  rcases hc with h | ⟨h1, h2⟩ <;> omega

/-- The `s1`/`s2` coefficient codomain: `[0, η] ∪ [q − η, q)` — the canonical-`ℤ_q` picture of
`[−η, η]`. -/
def etaRange (c : Nat) : Prop := c ≤ etaP ∨ (q - etaP ≤ c ∧ c < q)

/-- The `t0` coefficient codomain: `[0, 2^{d−1}] ∪ (q − 2^{d−1}, q)` — the canonical-`ℤ_q` picture of
`(−2^{d−1}, 2^{d−1}]`. -/
def t0Range (c : Nat) : Prop := c ≤ t0Half ∨ (q - t0Half < c ∧ c < q)

theorem bDecode_bEncode_eta (c : Nat) (hc : etaRange c) : bDecode etaP (bEncode etaP c) = c := by
  unfold etaRange at hc
  exact bDecode_bEncode etaP etaP c (le_refl _) (by unfold etaP; norm_num [Dregg2.Crypto.MlDsaRing.q]) hc

theorem bEncode_eta_lt (c : Nat) (hc : etaRange c) : bEncode etaP c < 2 ^ etaBits := by
  unfold etaRange at hc
  have h := bEncode_le etaP etaP c (le_refl _)
    (by unfold etaP; norm_num [Dregg2.Crypto.MlDsaRing.q]) hc
  have he : etaP = 4 := rfl
  have hb : (2 : Nat) ^ etaBits = 16 := by norm_num [Dregg2.Crypto.MlDsaKeygen.etaBits]
  omega

theorem bDecode_bEncode_t0 (c : Nat) (hc : t0Range c) : bDecode t0Half (bEncode t0Half c) = c := by
  unfold t0Range at hc
  refine bDecode_bEncode t0Half (t0Half - 1) c (by omega)
    (by unfold t0Half; norm_num [Dregg2.Crypto.MlDsaRing.q]) ?_
  have ht : t0Half = 4096 := rfl
  have hq : q = 8380417 := rfl
  rcases hc with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨by omega, h2⟩

theorem bEncode_t0_lt (c : Nat) (hc : t0Range c) : bEncode t0Half c < 2 ^ t0Bits := by
  unfold t0Range at hc
  have ht : t0Half = 4096 := rfl
  have hq : q = 8380417 := rfl
  have hcc : c ≤ t0Half ∨ (q - (t0Half - 1) ≤ c ∧ c < q) := by
    rcases hc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, h2⟩
  have h := bEncode_le t0Half (t0Half - 1) c (by omega)
    (by unfold t0Half; norm_num [Dregg2.Crypto.MlDsaRing.q]) hcc
  have hb : (2 : Nat) ^ t0Bits = 8192 := by norm_num [Dregg2.Crypto.MlDsaKeygen.t0Bits]
  omega

/-! ## §3 — `Power2Round` bounds (FIPS 204 Alg 35), unconditional in the input coefficient. -/

/-- **`t1` is 10 bits.** For EVERY `r`, the `Power2Round` high part is `< 2¹⁰` — including the
carry branch, which cannot fire at the top of `[0,q)` because `q − 1 = 1023·2¹³` is `2¹³`-aligned. -/
theorem power2round_t1_lt (r : Nat) : (power2round r).1 < 1024 := by
  unfold Dregg2.Crypto.MlDsaKeygen.power2round
  simp only [Dregg2.Crypto.MlDsaKeygen.twoD, Dregg2.Crypto.MlDsaKeygen.t0Half,
    Dregg2.Crypto.MlDsaRing.q]
  by_cases h : r % 8380417 % 8192 ≤ 4096 <;> simp [h] <;> omega

/-- **`t0` is centered.** For EVERY `r`, the `Power2Round` low part is in `[0, 2¹²] ∪ (q − 2¹², q)` —
the canonical-`ℤ_q` picture of `(−2¹², 2¹²]`. -/
theorem power2round_t0_range (r : Nat) : t0Range (power2round r).2 := by
  unfold t0Range Dregg2.Crypto.MlDsaKeygen.power2round
  simp only [Dregg2.Crypto.MlDsaKeygen.twoD, Dregg2.Crypto.MlDsaKeygen.t0Half,
    Dregg2.Crypto.MlDsaRing.q]
  by_cases h : r % 8380417 % 8192 ≤ 4096 <;> simp [h] <;> omega

/-! ## §4 — the generic `Id`-monad `forIn` INVARIANT tool (for the branching rejection loop). -/

/-- The state carried out of a `ForInStep`. -/
def stepState {σ : Type} : ForInStep σ → σ
  | .yield s => s
  | .done s => s

/-- **`forIn` invariant induction.** If every iteration `yield`s (never `done`s) and preserves `P`, the
whole loop preserves `P`. Unlike a `foldl` normalisation this tolerates arbitrary branching in the body —
which the FIPS 204 `RejBoundedPoly` loop has (two nested rejection tests). -/
theorem forIn_id_inv {σ : Type} (P : σ → Prop) (f : Nat → σ → Id (ForInStep σ))
    (hy : ∀ i s, (f i s : Id (ForInStep σ)) = ForInStep.yield (stepState (f i s)))
    (hstep : ∀ i s, P s → P (stepState (f i s))) :
    ∀ (l : List Nat) (init : σ), P init → P (forIn l init f : Id σ) := by
  intro l
  induction l with
  | nil => intro init h; exact h
  | cons a t ih =>
    intro init h
    rw [List.forIn_cons, hy a init]
    show P (forIn t (stepState (f a init)) f : Id σ)
    exact ih _ (hstep a init h)

/-! ## §5 — `ExpandS`: every sampled coefficient is in `[−η, η]` (FIPS 204 Alg 31/33). -/

/-- `CoeffFromHalfByte` (FIPS 204 Alg 15, η = 4) only ever produces coefficients in `[−η, η]`. -/
theorem coeffFromHalfByte_range (b c : Nat) (h : coeffFromHalfByte b = some c) : etaRange c := by
  unfold etaRange
  have hq : q = 8380417 := rfl
  have he : etaP = 4 := rfl
  rw [hq, he]
  unfold Dregg2.Crypto.MlDsaKeygen.coeffFromHalfByte at h
  by_cases h1 : b < 9
  · rw [if_pos h1] at h
    by_cases h2 : b ≤ 4
    · rw [if_pos h2] at h
      simp only [Option.some.injEq] at h
      rw [← h]; omega
    · rw [if_neg h2] at h
      simp only [Option.some.injEq] at h
      rw [← h]
      simp only [Dregg2.Crypto.MlDsaRing.q]
      omega
  · rw [if_neg h1] at h
    exact absurd h (by simp)

/-- One `push` preserves the `[−η, η]` invariant. -/
theorem etaRange_push (a : Array Nat) (c : Nat) (ha : ∀ j, j < a.size → etaRange (a[j]!))
    (hc : etaRange c) : ∀ j, j < (a.push c).size → etaRange ((a.push c)[j]!) := by
  intro j hj
  rw [Array.size_push] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
  · rw [getElem!_push_lt _ _ _ hlt]; exact ha j hlt
  · subst heq
    rw [getElem!_push_eq]
    exact hc

/-- TWO `push`es preserve it — the branch of `RejBoundedPoly` where BOTH nibbles of the stream byte are
accepted. (Stated separately so the invariant step closes by `exact` — defeq-tolerant — rather than by a
syntactic `rw`, which cannot see through the `ForInStep`/`Id` wrapper the `do`-block leaves behind.) -/
theorem etaRange_push2 (a : Array Nat) (c d : Nat) (ha : ∀ j, j < a.size → etaRange (a[j]!))
    (hc : etaRange c) (hd : etaRange d) :
    ∀ j, j < ((a.push c).push d).size → etaRange (((a.push c).push d)[j]!) :=
  etaRange_push _ _ (etaRange_push _ _ ha hc) hd

/-- **`RejBoundedPoly` stays in range, ∀ seed.** Every collected coefficient is in `[−η, η]` (canonical
`ℤ_q` rep) — a `forIn` invariant through the rejection loop, no assumption on the XOF stream. -/
theorem rejBoundedPoly_range (seed : List UInt8) :
    ∀ j, j < (rejBoundedPoly seed).size → etaRange ((rejBoundedPoly seed)[j]!) := by
  unfold Dregg2.Crypto.MlDsaKeygen.rejBoundedPoly
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, bind_pure_comp, id_map_apply, id_eq]
  refine forIn_id_inv (fun (s : Poly) => ∀ j, j < s.size → etaRange (s[j]!)) _ ?_ ?_ _ _ ?_
  · intro i s
    repeat' split
    all_goals rfl
  · intro i s hs
    repeat' split
    all_goals
      first
        | exact hs
        | exact etaRange_push _ _ hs
            (coeffFromHalfByte_range _ _ (by assumption))
        | exact etaRange_push2 _ _ _ hs
            (coeffFromHalfByte_range _ _ (by assumption))
            (coeffFromHalfByte_range _ _ (by assumption))
  · intro j hj
    simp at hj

/-- `ExpandS` unfolded: the two `push`-folds (`s1` over `ℓ`, `s2` over `k`). -/
theorem expandS_unfold (rhoP : List UInt8) :
    expandS rhoP =
      (List.foldl (fun s1 i => s1.push (rejBoundedPoly
          (rhoP ++ [UInt8.ofNat (i % 256), UInt8.ofNat (i / 256)])))
        (Array.mkEmpty paramL) (List.range' 0 paramL 1),
       List.foldl (fun s2 i => s2.push (rejBoundedPoly
          (rhoP ++ [UInt8.ofNat ((i + paramL) % 256), UInt8.ofNat ((i + paramL) / 256)])))
        (Array.mkEmpty paramK) (List.range' 0 paramK 1)) := by
  unfold Dregg2.Crypto.MlDsaKeygen.expandS
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl]
  rfl

theorem expandS_s1_size (rhoP : List UInt8) : (expandS rhoP).1.size = paramL := by
  rw [expandS_unfold]
  have h := (pushIdxFold_spec (fun i => rejBoundedPoly
      (rhoP ++ [UInt8.ofNat (i % 256), UInt8.ofNat (i / 256)])) paramL (Array.mkEmpty paramL)).1
  simpa [size_mkEmpty] using h

theorem expandS_s2_size (rhoP : List UInt8) : (expandS rhoP).2.size = paramK := by
  rw [expandS_unfold]
  have h := (pushIdxFold_spec (fun i => rejBoundedPoly
      (rhoP ++ [UInt8.ofNat ((i + paramL) % 256), UInt8.ofNat ((i + paramL) / 256)]))
      paramK (Array.mkEmpty paramK)).1
  simpa [size_mkEmpty] using h

theorem expandS_s1_get (rhoP : List UInt8) (i : Nat) (hi : i < paramL) :
    (expandS rhoP).1[i]! = rejBoundedPoly (rhoP ++ [UInt8.ofNat (i % 256), UInt8.ofNat (i / 256)]) := by
  rw [expandS_unfold]
  have h := (pushIdxFold_spec (fun i => rejBoundedPoly
      (rhoP ++ [UInt8.ofNat (i % 256), UInt8.ofNat (i / 256)])) paramL (Array.mkEmpty paramL)).2.2 i hi
  simpa [size_mkEmpty] using h

theorem expandS_s2_get (rhoP : List UInt8) (i : Nat) (hi : i < paramK) :
    (expandS rhoP).2[i]! = rejBoundedPoly
      (rhoP ++ [UInt8.ofNat ((i + paramL) % 256), UInt8.ofNat ((i + paramL) / 256)]) := by
  rw [expandS_unfold]
  have h := (pushIdxFold_spec (fun i => rejBoundedPoly
      (rhoP ++ [UInt8.ofNat ((i + paramL) % 256), UInt8.ofNat ((i + paramL) / 256)]))
      paramK (Array.mkEmpty paramK)).2.2 i hi
  simpa [size_mkEmpty] using h

/-- **`ExpandS` range, componentwise.** Every `s1` coefficient is in `[−η, η]`. -/
theorem expandS_s1_range (rhoP : List UInt8) (i : Nat) (hi : i < paramL) (j : Nat)
    (hj : j < ((expandS rhoP).1[i]!).size) : etaRange (((expandS rhoP).1[i]!)[j]!) := by
  rw [expandS_s1_get rhoP i hi] at hj ⊢
  exact rejBoundedPoly_range _ j hj

/-- **`ExpandS` range, componentwise.** Every `s2` coefficient is in `[−η, η]`. -/
theorem expandS_s2_range (rhoP : List UInt8) (i : Nat) (hi : i < paramK) (j : Nat)
    (hj : j < ((expandS rhoP).2[i]!).size) : etaRange (((expandS rhoP).2[i]!)[j]!) := by
  rw [expandS_s2_get rhoP i hi] at hj ⊢
  exact rejBoundedPoly_range _ j hj

/-! ## §6 — the `t1` / `t0` vectors: shape and per-coefficient bounds. -/

theorem p2rLoop_unfold (ti : Poly) :
    p2rLoop ti =
      (let r := List.foldl
        (fun (p : MProd Poly Poly) c => ⟨p.1.set! c (power2round (ti[c]!)).1,
          p.2.set! c (power2round (ti[c]!)).2⟩)
        (⟨zeroPoly, zeroPoly⟩ : MProd Poly Poly) (List.range' 0 256 1)
       (r.1, r.2)) := by
  unfold Dregg2.Crypto.MlDsaKeygen.p2rLoop
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl]
  rfl

theorem p2rLoop_sizes (ti : Poly) : (p2rLoop ti).1.size = 256 ∧ (p2rLoop ti).2.size = 256 := by
  rw [p2rLoop_unfold]
  obtain ⟨h1, h2, _, _⟩ := setIdxFold2_spec (fun c => (power2round (ti[c]!)).1)
    (fun c => (power2round (ti[c]!)).2) zeroPoly zeroPoly 256
  exact ⟨by simpa [zeroPoly_size] using h1, by simpa [zeroPoly_size] using h2⟩

theorem p2rLoop_t1_lt (ti : Poly) (j : Nat) (hj : j < 256) : (p2rLoop ti).1[j]! < 1024 := by
  rw [p2rLoop_unfold]
  obtain ⟨_, _, h1, _⟩ := setIdxFold2_spec (fun c => (power2round (ti[c]!)).1)
    (fun c => (power2round (ti[c]!)).2) zeroPoly zeroPoly 256
  have := h1 j hj (by rw [zeroPoly_size]; exact hj)
  simp only at this ⊢
  rw [this]
  exact power2round_t1_lt _

theorem p2rLoop_t0_range (ti : Poly) (j : Nat) (hj : j < 256) : t0Range ((p2rLoop ti).2[j]!) := by
  rw [p2rLoop_unfold]
  obtain ⟨_, _, _, h2⟩ := setIdxFold2_spec (fun c => (power2round (ti[c]!)).1)
    (fun c => (power2round (ti[c]!)).2) zeroPoly zeroPoly 256
  have := h2 j hj (by rw [zeroPoly_size]; exact hj)
  simp only at this ⊢
  rw [this]
  exact power2round_t0_range _

/-- **`tPairs` unfolded.** The single indexed `push`-fold. The spec applies by UNIFICATION — the per-row
value stays an abstract `f i` — so neither elaborator nor kernel ever reduces `p2rLoop`/`intt`/`matAcc`.
(This is why `tLoop` is built from a ONE-mutable `tPairs`: a two-`mut` `do`-loop normalises through an
`MProd` `forIn` whose rewrite the kernel cannot check here, deep-recursing on the symbolic 256-point
`intt`/`matAcc` loops carried by every iteration.) -/
theorem tPairs_size (aHat s1Hat s2 : Array Poly) : (tPairs aHat s1Hat s2).size = paramK := by
  unfold Dregg2.Crypto.MlDsaKeygen.tPairs
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl]
  have h := (pushIdxFold_spec (fun i => p2rLoop (addPoly (intt (matAcc aHat s1Hat i)) s2[i]!))
      paramK (Array.mkEmpty (α := Poly × Poly) paramK)).1
  simp only [size_mkEmpty, Nat.zero_add] at h
  exact h

/-- Row `i` of `tPairs` IS the `Power2Round` split of `NTT⁻¹(Â ∘ ŝ1)[i] + s2[i]`. -/
theorem tPairs_get (aHat s1Hat s2 : Array Poly) (i : Nat) (hi : i < paramK) :
    (tPairs aHat s1Hat s2)[i]! = p2rLoop (addPoly (intt (matAcc aHat s1Hat i)) s2[i]!) := by
  unfold Dregg2.Crypto.MlDsaKeygen.tPairs
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl]
  have h := (pushIdxFold_spec (fun i => p2rLoop (addPoly (intt (matAcc aHat s1Hat i)) s2[i]!))
      paramK (Array.mkEmpty (α := Poly × Poly) paramK)).2.2 i hi
  simp only [size_mkEmpty, Nat.zero_add] at h
  exact h

theorem tLoop_sizes (aHat s1Hat s2 : Array Poly) :
    (tLoop aHat s1Hat s2).1.size = paramK ∧ (tLoop aHat s1Hat s2).2.size = paramK := by
  unfold Dregg2.Crypto.MlDsaKeygen.tLoop
  refine ⟨?_, ?_⟩ <;> simp only [Array.size_map, tPairs_size]

theorem tLoop_t1_get (aHat s1Hat s2 : Array Poly) (i : Nat) (hi : i < paramK) :
    (tLoop aHat s1Hat s2).1[i]! = (p2rLoop (addPoly (intt (matAcc aHat s1Hat i)) s2[i]!)).1 := by
  unfold Dregg2.Crypto.MlDsaKeygen.tLoop
  show ((tPairs aHat s1Hat s2).map Prod.fst)[i]! = _
  rw [getElem!_map _ _ i (by rw [tPairs_size]; exact hi), tPairs_get aHat s1Hat s2 i hi]

theorem tLoop_t0_get (aHat s1Hat s2 : Array Poly) (i : Nat) (hi : i < paramK) :
    (tLoop aHat s1Hat s2).2[i]! = (p2rLoop (addPoly (intt (matAcc aHat s1Hat i)) s2[i]!)).2 := by
  unfold Dregg2.Crypto.MlDsaKeygen.tLoop
  show ((tPairs aHat s1Hat s2).map Prod.snd)[i]! = _
  rw [getElem!_map _ _ i (by rw [tPairs_size]; exact hi), tPairs_get aHat s1Hat s2 i hi]

/-! ## §7 — the ring keygen's fields, and the byte↔ring BRIDGES (definitional). -/

/-- `G = H(ξ ‖ k ‖ ℓ, 128)`. -/
def gOf (xi : List UInt8) : List UInt8 :=
  shake256 (xi ++ [UInt8.ofNat paramK, UInt8.ofNat paramL]) 128
/-- `ρ` — the `ExpandA` seed. -/
def rhoOf (xi : List UInt8) : List UInt8 := (gOf xi).take 32
/-- `ρ′` — the `ExpandS` seed. -/
def rhoPOf (xi : List UInt8) : List UInt8 := ((gOf xi).drop 32).take 64
/-- `K` — the signing seed. -/
def kkOf (xi : List UInt8) : List UInt8 := (gOf xi).drop 96

theorem ring_rho (xi : List UInt8) : (mldsaKeygenRing xi).rho = rhoOf xi := rfl
theorem ring_kk (xi : List UInt8) : (mldsaKeygenRing xi).kk = kkOf xi := rfl
theorem ring_s1 (xi : List UInt8) : (mldsaKeygenRing xi).s1 = (expandS (rhoPOf xi)).1 := rfl
theorem ring_s2 (xi : List UInt8) : (mldsaKeygenRing xi).s2 = (expandS (rhoPOf xi)).2 := rfl
theorem ring_t1 (xi : List UInt8) : (mldsaKeygenRing xi).t1 =
    (tLoop (expandA (rhoOf xi)) (s1HatOf (expandS (rhoPOf xi)).1) (expandS (rhoPOf xi)).2).1 := rfl
theorem ring_t0 (xi : List UInt8) : (mldsaKeygenRing xi).t0 =
    (tLoop (expandA (rhoOf xi)) (s1HatOf (expandS (rhoPOf xi)).1) (expandS (rhoPOf xi)).2).2 := rfl

/-- **Bridge**: the byte `pk` is `pkEncode` of the RING `(ρ, t1)` (definitional — `mldsaKeygenInternal`
IS `mldsaKeygenRing` composed with the codec). -/
theorem bridge_pk (xi : List UInt8) :
    (mldsaKeygenInternal xi).1 = pkEncode ((mldsaKeygenRing xi).rho, (mldsaKeygenRing xi).t1) := rfl

/-- `tr = H(pk, 64)`. -/
def trOf (xi : List UInt8) : List UInt8 := shake256 (mldsaKeygenInternal xi).1 64

/-- **Bridge**: the byte `sk` is `skEncode` of the RING `(ρ, K, s1, s2, t0)` and `tr`. -/
theorem bridge_sk (xi : List UInt8) :
    (mldsaKeygenInternal xi).2 =
      skEncode (mldsaKeygenRing xi).rho (mldsaKeygenRing xi).kk (trOf xi)
        (mldsaKeygenRing xi).s1 (mldsaKeygenRing xi).s2 (mldsaKeygenRing xi).t0 := rfl

/-- `|ρ| = 32` (FIPS 202 fixed output length; `|G| = 128`). -/
theorem rhoOf_length (xi : List UInt8) : (rhoOf xi).length = 32 := by
  unfold rhoOf gOf
  rw [List.length_take, shake256_length]
  omega

/-- `|K| = 32`. -/
theorem kkOf_length (xi : List UInt8) : (kkOf xi).length = 32 := by
  unfold kkOf gOf
  rw [List.length_drop, shake256_length]

/-- `|tr| = 64`. -/
theorem trOf_length (xi : List UInt8) : (trOf xi).length = 64 := by
  unfold trOf
  rw [shake256_length]

/-! ## §8 — the `sk` byte layout and its round-trip (FIPS 204 Alg 24/25). -/

/-- Bytes per packed `s1`/`s2` polynomial (`256·4/8`). -/
def etaPolyBytes : Nat := 128
/-- Bytes per packed `t0` polynomial (`256·13/8`). -/
def t0PolyBytes : Nat := 416

/-- `BitUnpack(·, η, η)` of one 128-byte block: unpack 4-bit fields, then the sign map. -/
def unpackEta (b : Array UInt8) (off : Nat) : Poly :=
  (unpackBits b off 256 etaBits).map (bDecode etaP)

/-- `BitUnpack(·, 2^{d−1}−1, 2^{d−1})` of one 416-byte block. -/
def unpackT0 (b : Array UInt8) (off : Nat) : Poly :=
  (unpackBits b off 256 t0Bits).map (bDecode t0Half)

/-- **`skDecode` — FIPS 204 Algorithm 25** at the ML-DSA-65 parameters: split the 4032-byte secret key
back into `(ρ, K, tr, s1, s2, t0)`. -/
def skDecode (sk : List UInt8) :
    (List UInt8 × List UInt8 × List UInt8 × Array Poly × Array Poly × Array Poly) := Id.run do
  let b := sk.toArray
  let rho := (b.extract 0 32).toList
  let kk := (b.extract 32 64).toList
  let tr := (b.extract 64 128).toList
  let mut s1 : Array Poly := Array.mkEmpty paramL
  for i in [0:paramL] do
    s1 := s1.push (unpackEta b (128 + i * etaPolyBytes))
  let mut s2 : Array Poly := Array.mkEmpty paramK
  for i in [0:paramK] do
    s2 := s2.push (unpackEta b (128 + (paramL + i) * etaPolyBytes))
  let mut t0 : Array Poly := Array.mkEmpty paramK
  for i in [0:paramK] do
    t0 := t0.push (unpackT0 b (128 + (paramL + paramK) * etaPolyBytes + i * t0PolyBytes))
  return (rho, kk, tr, s1, s2, t0)

theorem skDecode_unfold (sk : List UInt8) :
    skDecode sk =
      ((sk.toArray.extract 0 32).toList, (sk.toArray.extract 32 64).toList,
       (sk.toArray.extract 64 128).toList,
       List.foldl (fun s1 i => s1.push (unpackEta sk.toArray (128 + i * etaPolyBytes)))
         (Array.mkEmpty paramL) (List.range' 0 paramL 1),
       List.foldl (fun s2 i => s2.push (unpackEta sk.toArray (128 + (paramL + i) * etaPolyBytes)))
         (Array.mkEmpty paramK) (List.range' 0 paramK 1),
       List.foldl (fun t0 i => t0.push
           (unpackT0 sk.toArray (128 + (paramL + paramK) * etaPolyBytes + i * t0PolyBytes)))
         (Array.mkEmpty paramK) (List.range' 0 paramK 1)) := by
  unfold skDecode
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl]
  rfl

theorem skEncode_unfold (rho kk tr : List UInt8) (s1 s2 t0 : Array Poly) :
    skEncode rho kk tr s1 s2 t0 =
      List.foldl (fun sk i => sk ++ (packT0 t0[i]!).toList)
        (List.foldl (fun sk i => sk ++ (packEta s2[i]!).toList)
          (List.foldl (fun sk i => sk ++ (packEta s1[i]!).toList)
            (rho ++ kk ++ tr) (List.range' 0 paramL 1))
          (List.range' 0 paramK 1))
        (List.range' 0 paramK 1) := by
  unfold Dregg2.Crypto.MlDsaKeygen.skEncode
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl]
  rfl

/-- `packEta` emits exactly 128 bytes on a size-256 polynomial. -/
theorem packEta_size (p : Poly) (hp : p.size = 256) : (packEta p).size = etaPolyBytes := by
  unfold Dregg2.Crypto.MlDsaKeygen.packEta
  rw [packBits_size, Array.size_map, hp]
  rfl

/-- `packT0` emits exactly 416 bytes on a size-256 polynomial. -/
theorem packT0_size (p : Poly) (hp : p.size = 256) : (packT0 p).size = t0PolyBytes := by
  unfold Dregg2.Crypto.MlDsaKeygen.packT0
  rw [packBits_size, Array.size_map, hp]
  rfl

/-- **One `s1`/`s2` block round-trips**: `BitUnpack ∘ BitPack = id` on a size-256 polynomial whose
coefficients are in `[−η, η]`. -/
theorem unpackEta_packEta (p : Poly) (hp : p.size = 256) (hr : ∀ j, j < 256 → etaRange (p[j]!)) :
    unpackEta (packEta p) 0 = p := by
  unfold unpackEta Dregg2.Crypto.MlDsaKeygen.packEta
  rw [unpackBits_packBits _ _ (by rw [Array.size_map, hp])
    (by intro j hj
        rw [getElem!_map _ _ j (by rw [hp]; exact hj)]
        exact bEncode_eta_lt _ (hr j hj))]
  exact map_map_cancel p _ _ (by intro j hj; rw [hp] at hj; exact bDecode_bEncode_eta _ (hr j hj))

/-- **One `t0` block round-trips**. -/
theorem unpackT0_packT0 (p : Poly) (hp : p.size = 256) (hr : ∀ j, j < 256 → t0Range (p[j]!)) :
    unpackT0 (packT0 p) 0 = p := by
  unfold unpackT0 Dregg2.Crypto.MlDsaKeygen.packT0
  rw [unpackBits_packBits _ _ (by rw [Array.size_map, hp])
    (by intro j hj
        rw [getElem!_map _ _ j (by rw [hp]; exact hj)]
        exact bEncode_t0_lt _ (hr j hj))]
  exact map_map_cancel p _ _ (by intro j hj; rw [hp] at hj; exact bDecode_bEncode_t0 _ (hr j hj))

/-! ## §9 — the `pk` leg: `pkDecode ∘ pkEncode` on the RING `t1`, UNCONDITIONAL.

`pkEncode` writes `ρ(32) ‖ SimpleBitPack₁₀(t1₀) ‖ … ‖ SimpleBitPack₁₀(t1₅)`; `CodecRoundTrip.pkDecode_pkEncode`
inverts that layout for any 32-byte `ρ` and any `k = 6` size-256 `t1` polys with coefficients `< 2¹⁰`. All
three well-formedness facts are DISCHARGED here on the RING generator: `|ρ| = 32` from the FIPS 202
squeeze-length theorem, the shape from the `tLoop`/`p2rLoop` fold specs, and the coefficient bound from
`power2round_t1_lt`. -/

theorem ring_t1_size (xi : List UInt8) : (mldsaKeygenRing xi).t1.size = paramK := by
  rw [ring_t1]; exact (tLoop_sizes _ _ _).1

theorem ring_t0_size (xi : List UInt8) : (mldsaKeygenRing xi).t0.size = paramK := by
  rw [ring_t0]; exact (tLoop_sizes _ _ _).2

theorem ring_t1_poly_size (xi : List UInt8) (i : Nat) (hi : i < paramK) :
    ((mldsaKeygenRing xi).t1[i]!).size = 256 := by
  rw [ring_t1, tLoop_t1_get _ _ _ i hi]; exact (p2rLoop_sizes _).1

theorem ring_t0_poly_size (xi : List UInt8) (i : Nat) (hi : i < paramK) :
    ((mldsaKeygenRing xi).t0[i]!).size = 256 := by
  rw [ring_t0, tLoop_t0_get _ _ _ i hi]; exact (p2rLoop_sizes _).2

/-- **The `t1` coefficient bound on the RING key**: every high part is `< 2^{t1Bits} = 2¹⁰` — the
`SimpleBitUnpack` codomain the `pk` codec needs. -/
theorem ring_t1_lt (xi : List UInt8) (i : Nat) (hi : i < paramK) (j : Nat) (hj : j < 256) :
    ((mldsaKeygenRing xi).t1[i]!)[j]! < 2 ^ t1Bits := by
  have hb : (2 : Nat) ^ t1Bits = 1024 := by norm_num [Dregg2.Crypto.MlDsaCodec.t1Bits]
  rw [hb, ring_t1, tLoop_t1_get _ _ _ i hi]
  exact p2rLoop_t1_lt _ j hj

/-- **The `t0` coefficient codomain on the RING key**: every low part is in `[0,2¹²] ∪ (q−2¹², q)`. -/
theorem ring_t0_range (xi : List UInt8) (i : Nat) (hi : i < paramK) (j : Nat) (hj : j < 256) :
    t0Range (((mldsaKeygenRing xi).t0[i]!)[j]!) := by
  rw [ring_t0, tLoop_t0_get _ _ _ i hi]
  exact p2rLoop_t0_range _ j hj

/-- **THE `pk` REFINEMENT — UNCONDITIONAL, ∀ ξ.** Decoding the emitted 1952-byte public key recovers
EXACTLY the RING-level `(ρ, t1)` that `mldsaKeygenRing` (ExpandA/ExpandS/NTT/matvec/Power2Round) computes.
No hypothesis: the `ρ`-length fact is FIPS 202, the shape and the `2¹⁰` bound are the loop specs. -/
theorem mldsaKeygen_pk_refines_ring (xi : List UInt8) :
    pkDecode (mldsaKeygenInternal xi).1 = ((mldsaKeygenRing xi).rho, (mldsaKeygenRing xi).t1) := by
  rw [bridge_pk]
  exact pkDecode_pkEncode _ _ (by rw [ring_rho]; exact rhoOf_length xi) (ring_t1_size xi)
    (ring_t1_poly_size xi) (ring_t1_lt xi)

/-! ## §10 — the `sk` byte layout `ρ ‖ K ‖ tr ‖ BitPack(s1) ‖ BitPack(s2) ‖ BitPack(t0)`, and its inverse.

FIPS 204 Algorithm 24 emits the 4032-byte secret key as a PREFIX (`32+32+64 = 128` bytes) followed by three
uniform block regions: `ℓ = 5` `η`-packed 128-byte `s1` blocks, `k = 6` `η`-packed 128-byte `s2` blocks, and
`k = 6` 13-bit-packed 416-byte `t0` blocks. Each region is an `appendFold_spec` instance; `unpackBits` reads
only its own `count·cbits/8`-byte window (`unpackBits_eq_of_window`), so each block decodes independently
through §8's `unpackEta_packEta` / `unpackT0_packT0`. -/

/-- The `sk` prefix `ρ ‖ K ‖ tr` followed by the `ℓ` packed `s1` blocks. -/
def skA1 (rho kk tr : List UInt8) (s1 : Array Poly) : Array UInt8 :=
  List.foldl (fun out i => out ++ packEta s1[i]!) (rho ++ kk ++ tr).toArray (List.range' 0 paramL 1)

/-- … then the `k` packed `s2` blocks. -/
def skA2 (rho kk tr : List UInt8) (s1 s2 : Array Poly) : Array UInt8 :=
  List.foldl (fun out i => out ++ packEta s2[i]!) (skA1 rho kk tr s1) (List.range' 0 paramK 1)

/-- … then the `k` packed `t0` blocks: the WHOLE 4032-byte secret key, as an `Array`. -/
def skA3 (rho kk tr : List UInt8) (s1 s2 t0 : Array Poly) : Array UInt8 :=
  List.foldl (fun out i => out ++ packT0 t0[i]!) (skA2 rho kk tr s1 s2) (List.range' 0 paramK 1)

/-- `skEncode`'s `List`-append assembly IS the `Array`-append layout `skA3` (`toArray` is a monoid map). -/
theorem skEncode_toArray (rho kk tr : List UInt8) (s1 s2 t0 : Array Poly) :
    (skEncode rho kk tr s1 s2 t0).toArray = skA3 rho kk tr s1 s2 t0 := by
  rw [skEncode_unfold, listAppendFold_toArray (fun i => (packT0 t0[i]!).toList) paramK,
      listAppendFold_toArray (fun i => (packEta s2[i]!).toList) paramK,
      listAppendFold_toArray (fun i => (packEta s1[i]!).toList) paramL]
  simp only [Array.toArray_toList]
  rfl

theorem prefix_size (rho kk tr : List UInt8) (hrho : rho.length = 32) (hkk : kk.length = 32)
    (htr : tr.length = 64) : ((rho ++ kk ++ tr).toArray).size = 128 := by
  have h : (rho ++ kk ++ tr).length = 128 := by
    rw [List.length_append, List.length_append, hrho, hkk, htr]
  simpa using h

theorem prefix_toArray (rho kk tr : List UInt8) :
    (rho ++ kk ++ tr).toArray = (rho.toArray ++ kk.toArray) ++ tr.toArray := by
  simp [List.append_toArray]

theorem prefix_get_rho (rho kk tr : List UInt8) (hrho : rho.length = 32) (j : Nat) (hj : j < 32) :
    (rho ++ kk ++ tr).toArray[j]! = rho.toArray[j]! := by
  rw [prefix_toArray,
      getElem!_append_left _ _ _
        (by rw [Array.size_append, List.size_toArray, List.size_toArray, hrho]; omega),
      getElem!_append_left _ _ _ (by rw [List.size_toArray, hrho]; exact hj)]

theorem prefix_get_kk (rho kk tr : List UInt8) (hrho : rho.length = 32) (hkk : kk.length = 32)
    (j : Nat) (hj : j < 32) : (rho ++ kk ++ tr).toArray[32 + j]! = kk.toArray[j]! := by
  rw [prefix_toArray,
      getElem!_append_left _ _ _
        (by rw [Array.size_append, List.size_toArray, List.size_toArray, hrho, hkk]; omega),
      getElem!_append_right _ _ _ (by rw [List.size_toArray, hrho]; omega)
        (by rw [List.size_toArray, List.size_toArray, hrho, hkk]; omega),
      show 32 + j - rho.toArray.size = j from by rw [List.size_toArray, hrho]; omega]

theorem prefix_get_tr (rho kk tr : List UInt8) (hrho : rho.length = 32) (hkk : kk.length = 32)
    (htr : tr.length = 64) (j : Nat) (hj : j < 64) :
    (rho ++ kk ++ tr).toArray[64 + j]! = tr.toArray[j]! := by
  rw [prefix_toArray,
      getElem!_append_right _ _ _
        (by rw [Array.size_append, List.size_toArray, List.size_toArray, hrho, hkk]; omega)
        (by rw [Array.size_append, List.size_toArray, List.size_toArray, List.size_toArray,
                hrho, hkk, htr]; omega),
      show 64 + j - (rho.toArray ++ kk.toArray).size = j from by
        rw [Array.size_append, List.size_toArray, List.size_toArray, hrho, hkk]; omega]

/-- A byte window of `E` that agrees with `l` recovers `l` on `extract`. -/
theorem extract_toList_eq (E : Array UInt8) (l : List UInt8) (base len : Nat)
    (hl : l.length = len) (hE : base + len ≤ E.size)
    (h : ∀ j, j < len → E[base + j]! = l.toArray[j]!) :
    (E.extract base (base + len)).toList = l := by
  have hx : E.extract base (base + len) = l.toArray := by
    apply arrayExtAll
    · rw [Array.size_extract, Nat.min_eq_left hE, List.size_toArray, hl]; omega
    · intro j hj
      rw [Array.size_extract, Nat.min_eq_left hE] at hj
      rw [getElem!_extract _ _ _ _ (by rw [Nat.min_eq_left hE]; omega)]
      exact h j (by omega)
  rw [hx]

/-! ### The three block regions of `sk`, by `appendFold_spec`. -/

theorem skA1_spec (rho kk tr : List UInt8) (s1 : Array Poly)
    (hpre : ((rho ++ kk ++ tr).toArray).size = 128)
    (hs1sz : ∀ i, i < paramL → (s1[i]!).size = 256) :
    (skA1 rho kk tr s1).size = 768
    ∧ (∀ j, j < 128 → (skA1 rho kk tr s1)[j]! = ((rho ++ kk ++ tr).toArray)[j]!)
    ∧ (∀ i, i < paramL → ∀ j, j < 128 →
        (skA1 rho kk tr s1)[128 + i * 128 + j]! = (packEta s1[i]!)[j]!) := by
  obtain ⟨hsz, hlo, hhi⟩ := appendFold_spec (fun i => packEta s1[i]!) etaPolyBytes
    ((rho ++ kk ++ tr).toArray) paramL (fun i hi => packEta_size _ (hs1sz i hi))
  rw [hpre] at hsz hlo hhi
  exact ⟨hsz, hlo, hhi⟩

theorem skA2_spec (rho kk tr : List UInt8) (s1 s2 : Array Poly)
    (hpre : ((rho ++ kk ++ tr).toArray).size = 128)
    (hs1sz : ∀ i, i < paramL → (s1[i]!).size = 256)
    (hs2sz : ∀ i, i < paramK → (s2[i]!).size = 256) :
    (skA2 rho kk tr s1 s2).size = 1536
    ∧ (∀ j, j < 768 → (skA2 rho kk tr s1 s2)[j]! = (skA1 rho kk tr s1)[j]!)
    ∧ (∀ i, i < paramK → ∀ j, j < 128 →
        (skA2 rho kk tr s1 s2)[768 + i * 128 + j]! = (packEta s2[i]!)[j]!) := by
  obtain ⟨hsz, hlo, hhi⟩ := appendFold_spec (fun i => packEta s2[i]!) etaPolyBytes
    (skA1 rho kk tr s1) paramK (fun i hi => packEta_size _ (hs2sz i hi))
  rw [(skA1_spec rho kk tr s1 hpre hs1sz).1] at hsz hlo hhi
  exact ⟨hsz, hlo, hhi⟩

theorem skA3_spec (rho kk tr : List UInt8) (s1 s2 t0 : Array Poly)
    (hpre : ((rho ++ kk ++ tr).toArray).size = 128)
    (hs1sz : ∀ i, i < paramL → (s1[i]!).size = 256)
    (hs2sz : ∀ i, i < paramK → (s2[i]!).size = 256)
    (ht0sz : ∀ i, i < paramK → (t0[i]!).size = 256) :
    (skA3 rho kk tr s1 s2 t0).size = 4032
    ∧ (∀ j, j < 1536 → (skA3 rho kk tr s1 s2 t0)[j]! = (skA2 rho kk tr s1 s2)[j]!)
    ∧ (∀ i, i < paramK → ∀ j, j < 416 →
        (skA3 rho kk tr s1 s2 t0)[1536 + i * 416 + j]! = (packT0 t0[i]!)[j]!) := by
  obtain ⟨hsz, hlo, hhi⟩ := appendFold_spec (fun i => packT0 t0[i]!) t0PolyBytes
    (skA2 rho kk tr s1 s2) paramK (fun i hi => packT0_size _ (ht0sz i hi))
  rw [(skA2_spec rho kk tr s1 s2 hpre hs1sz hs2sz).1] at hsz hlo hhi
  exact ⟨hsz, hlo, hhi⟩

/-! ### The four regions, read through the WHOLE `sk`. -/

theorem skA3_prefix (rho kk tr : List UInt8) (s1 s2 t0 : Array Poly)
    (hpre : ((rho ++ kk ++ tr).toArray).size = 128)
    (hs1sz : ∀ i, i < paramL → (s1[i]!).size = 256)
    (hs2sz : ∀ i, i < paramK → (s2[i]!).size = 256)
    (ht0sz : ∀ i, i < paramK → (t0[i]!).size = 256) (j : Nat) (hj : j < 128) :
    (skA3 rho kk tr s1 s2 t0)[j]! = ((rho ++ kk ++ tr).toArray)[j]! := by
  rw [(skA3_spec rho kk tr s1 s2 t0 hpre hs1sz hs2sz ht0sz).2.1 j (by omega),
      (skA2_spec rho kk tr s1 s2 hpre hs1sz hs2sz).2.1 j (by omega),
      (skA1_spec rho kk tr s1 hpre hs1sz).2.1 j hj]

theorem skA3_s1 (rho kk tr : List UInt8) (s1 s2 t0 : Array Poly)
    (hpre : ((rho ++ kk ++ tr).toArray).size = 128)
    (hs1sz : ∀ i, i < paramL → (s1[i]!).size = 256)
    (hs2sz : ∀ i, i < paramK → (s2[i]!).size = 256)
    (ht0sz : ∀ i, i < paramK → (t0[i]!).size = 256)
    (i : Nat) (hi : i < paramL) (j : Nat) (hj : j < 128) :
    (skA3 rho kk tr s1 s2 t0)[128 + i * 128 + j]! = (packEta s1[i]!)[j]! := by
  have hi5 : i < 5 := hi
  rw [(skA3_spec rho kk tr s1 s2 t0 hpre hs1sz hs2sz ht0sz).2.1 _ (by omega),
      (skA2_spec rho kk tr s1 s2 hpre hs1sz hs2sz).2.1 _ (by omega),
      (skA1_spec rho kk tr s1 hpre hs1sz).2.2 i hi j hj]

theorem skA3_s2 (rho kk tr : List UInt8) (s1 s2 t0 : Array Poly)
    (hpre : ((rho ++ kk ++ tr).toArray).size = 128)
    (hs1sz : ∀ i, i < paramL → (s1[i]!).size = 256)
    (hs2sz : ∀ i, i < paramK → (s2[i]!).size = 256)
    (ht0sz : ∀ i, i < paramK → (t0[i]!).size = 256)
    (i : Nat) (hi : i < paramK) (j : Nat) (hj : j < 128) :
    (skA3 rho kk tr s1 s2 t0)[768 + i * 128 + j]! = (packEta s2[i]!)[j]! := by
  have hi6 : i < 6 := hi
  rw [(skA3_spec rho kk tr s1 s2 t0 hpre hs1sz hs2sz ht0sz).2.1 _ (by omega),
      (skA2_spec rho kk tr s1 s2 hpre hs1sz hs2sz).2.2 i hi j hj]

/-! ### One block, decoded: `unpackBits` sees only its own window. -/

/-- If `b` carries the 128 bytes of `BitPack(p, η, η)` at `off`, then `BitUnpack` at `off` recovers `p`. -/
theorem unpackEta_window (b : Array UInt8) (off : Nat) (p : Poly) (hp : p.size = 256)
    (hr : ∀ j, j < 256 → etaRange (p[j]!))
    (h : ∀ i, i < 128 → b[off + i]! = (packEta p)[i]!) :
    unpackEta b off = p := by
  unfold unpackEta
  rw [unpackBits_eq_of_window b (packEta p) off 0 256 etaBits
    (by intro i hi
        have hw : 256 * etaBits / 8 = 128 := rfl
        rw [hw] at hi
        rw [Nat.zero_add]
        exact h i hi)]
  exact unpackEta_packEta p hp hr

/-- If `b` carries the 416 bytes of `BitPack(p, 2^{d−1}−1, 2^{d−1})` at `off`, `BitUnpack` recovers `p`. -/
theorem unpackT0_window (b : Array UInt8) (off : Nat) (p : Poly) (hp : p.size = 256)
    (hr : ∀ j, j < 256 → t0Range (p[j]!))
    (h : ∀ i, i < 416 → b[off + i]! = (packT0 p)[i]!) :
    unpackT0 b off = p := by
  unfold unpackT0
  rw [unpackBits_eq_of_window b (packT0 p) off 0 256 t0Bits
    (by intro i hi
        have hw : 256 * t0Bits / 8 = 416 := rfl
        rw [hw] at hi
        rw [Nat.zero_add]
        exact h i hi)]
  exact unpackT0_packT0 p hp hr

/-! ## §11 — `skDecode ∘ skEncode = id` on well-formed key material (FIPS 204 Alg 24/25). -/

/-- **THE `sk` CODEC ROUND-TRIP, ∀.** For any 32-byte `ρ`/`K`, 64-byte `tr`, `ℓ` size-256 `s1` polys and
`k` size-256 `s2` polys whose coefficients lie in the `BitPack(·,η,η)` codomain `[−η,η]`, and `k` size-256
`t0` polys in the `BitPack(·,2^{d−1}−1,2^{d−1})` codomain `(−2^{d−1}, 2^{d−1}]`:
`skDecode (skEncode ρ K tr s1 s2 t0) = (ρ, K, tr, s1, s2, t0)`. Proved through the real block layout and the
mixed-radix codec inverse, NOT by `rfl` or `native_decide`. -/
theorem skDecode_skEncode (rho kk tr : List UInt8) (s1 s2 t0 : Array Poly)
    (hrho : rho.length = 32) (hkk : kk.length = 32) (htr : tr.length = 64)
    (hs1 : s1.size = paramL) (hs2 : s2.size = paramK) (ht0 : t0.size = paramK)
    (hs1sz : ∀ i, i < paramL → (s1[i]!).size = 256)
    (hs2sz : ∀ i, i < paramK → (s2[i]!).size = 256)
    (ht0sz : ∀ i, i < paramK → (t0[i]!).size = 256)
    (hs1r : ∀ i, i < paramL → ∀ j, j < 256 → etaRange ((s1[i]!)[j]!))
    (hs2r : ∀ i, i < paramK → ∀ j, j < 256 → etaRange ((s2[i]!)[j]!))
    (ht0r : ∀ i, i < paramK → ∀ j, j < 256 → t0Range ((t0[i]!)[j]!)) :
    skDecode (skEncode rho kk tr s1 s2 t0) = (rho, kk, tr, s1, s2, t0) := by
  have hpre : ((rho ++ kk ++ tr).toArray).size = 128 := prefix_size rho kk tr hrho hkk htr
  have hsz : (skA3 rho kk tr s1 s2 t0).size = 4032 :=
    (skA3_spec rho kk tr s1 s2 t0 hpre hs1sz hs2sz ht0sz).1
  rw [skDecode_unfold, skEncode_toArray]
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ρ
    exact extract_toList_eq _ rho 0 32 hrho (by rw [hsz]; omega)
      (fun j hj => by
        rw [Nat.zero_add, skA3_prefix rho kk tr s1 s2 t0 hpre hs1sz hs2sz ht0sz j (by omega)]
        exact prefix_get_rho rho kk tr hrho j hj)
  · -- K
    exact extract_toList_eq _ kk 32 32 hkk (by rw [hsz]; omega)
      (fun j hj => by
        rw [skA3_prefix rho kk tr s1 s2 t0 hpre hs1sz hs2sz ht0sz (32 + j) (by omega)]
        exact prefix_get_kk rho kk tr hrho hkk j hj)
  · -- tr
    exact extract_toList_eq _ tr 64 64 htr (by rw [hsz]; omega)
      (fun j hj => by
        rw [skA3_prefix rho kk tr s1 s2 t0 hpre hs1sz hs2sz ht0sz (64 + j) (by omega)]
        exact prefix_get_tr rho kk tr hrho hkk htr j hj)
  · -- s1
    obtain ⟨hfsz, _, hfget⟩ := pushIdxFold_spec
      (fun i => unpackEta (skA3 rho kk tr s1 s2 t0) (128 + i * etaPolyBytes)) paramL
      (Array.mkEmpty (α := Poly) paramL)
    rw [size_mkEmpty, Nat.zero_add] at hfsz
    simp only [size_mkEmpty, Nat.zero_add] at hfget
    apply arrayExtAll
    · rw [hfsz, hs1]
    · intro i hi
      rw [hfsz] at hi
      rw [hfget i hi]
      exact unpackEta_window _ _ _ (hs1sz i hi) (hs1r i hi)
        (fun j hj => skA3_s1 rho kk tr s1 s2 t0 hpre hs1sz hs2sz ht0sz i hi j hj)
  · -- s2
    obtain ⟨hfsz, _, hfget⟩ := pushIdxFold_spec
      (fun i => unpackEta (skA3 rho kk tr s1 s2 t0) (128 + (paramL + i) * etaPolyBytes)) paramK
      (Array.mkEmpty (α := Poly) paramK)
    rw [size_mkEmpty, Nat.zero_add] at hfsz
    simp only [size_mkEmpty, Nat.zero_add] at hfget
    apply arrayExtAll
    · rw [hfsz, hs2]
    · intro i hi
      rw [hfsz] at hi
      rw [hfget i hi]
      have hoff : 128 + (paramL + i) * etaPolyBytes = 768 + i * 128 := by
        show 128 + (5 + i) * 128 = 768 + i * 128
        omega
      rw [hoff]
      exact unpackEta_window _ _ _ (hs2sz i hi) (hs2r i hi)
        (fun j hj => skA3_s2 rho kk tr s1 s2 t0 hpre hs1sz hs2sz ht0sz i hi j hj)
  · -- t0
    obtain ⟨hfsz, _, hfget⟩ := pushIdxFold_spec
      (fun i => unpackT0 (skA3 rho kk tr s1 s2 t0)
        (128 + (paramL + paramK) * etaPolyBytes + i * t0PolyBytes)) paramK
      (Array.mkEmpty (α := Poly) paramK)
    rw [size_mkEmpty, Nat.zero_add] at hfsz
    simp only [size_mkEmpty, Nat.zero_add] at hfget
    apply arrayExtAll
    · rw [hfsz, ht0]
    · intro i hi
      rw [hfsz] at hi
      rw [hfget i hi]
      exact unpackT0_window _ _ _ (ht0sz i hi) (ht0r i hi)
        (fun j hj =>
          (skA3_spec rho kk tr s1 s2 t0 hpre hs1sz hs2sz ht0sz).2.2 i hi j hj)

/-! ## §12 — THE ONE NAMED, UNDISCHARGED LEG: `RejBoundedPoly` fills its 256 slots.

FIPS 204 Algorithm 31 collects 256 coefficients by REJECTION from a FIXED 512-byte SHAKE-256 prefix. That the
budget suffices is a property OF THE XOF OUTPUT on the actual seed, not a theorem: an adversarial nibble
stream (all `≥ 9`) would yield fewer, and `skEncode` would then pack short blocks. So the `s1`/`s2` SHAPE is
carried as the EXPLICIT hypothesis `ExpandSSized` — NOT a `sorry`, NOT an axiom. Everything else in the
refinement (the codomains, the layout, the codec inversion) is proved unconditionally. -/

/-- **NAMED HYPOTHESIS.** The `ExpandS` rejection sampler fills all 256 coefficient slots of every `s1`/`s2`
polynomial for THIS `ξ`. (`(expandS (rhoPOf ξ)).1[i]!` is definitionally `(mldsaKeygenRing ξ).s1[i]!`.) -/
def ExpandSSized (xi : List UInt8) : Prop :=
  (∀ i, i < paramL → ((expandS (rhoPOf xi)).1[i]!).size = 256)
  ∧ (∀ i, i < paramK → ((expandS (rhoPOf xi)).2[i]!).size = 256)

theorem ring_s1_size (xi : List UInt8) : (mldsaKeygenRing xi).s1.size = paramL := by
  rw [ring_s1]; exact expandS_s1_size _

theorem ring_s2_size (xi : List UInt8) : (mldsaKeygenRing xi).s2.size = paramK := by
  rw [ring_s2]; exact expandS_s2_size _

theorem ring_s1_range (xi : List UInt8) (hS : ExpandSSized xi) (i : Nat) (hi : i < paramL)
    (j : Nat) (hj : j < 256) : etaRange (((mldsaKeygenRing xi).s1[i]!)[j]!) := by
  rw [ring_s1]
  exact expandS_s1_range _ i hi j (by rw [hS.1 i hi]; exact hj)

theorem ring_s2_range (xi : List UInt8) (hS : ExpandSSized xi) (i : Nat) (hi : i < paramK)
    (j : Nat) (hj : j < 256) : etaRange (((mldsaKeygenRing xi).s2[i]!)[j]!) := by
  rw [ring_s2]
  exact expandS_s2_range _ i hi j (by rw [hS.2 i hi]; exact hj)

/-! ## §13 — THE ML-DSA-65 KeyGen BYTE↔RING REFINEMENT. -/

/-- **THE KeyGen REFINEMENT, ∀ ξ (modulo the one named `ExpandSSized` leg).** For EVERY seed `ξ`:

* decoding the emitted 1952-byte `pk` recovers EXACTLY the RING-level `(ρ, t1)`, and
* decoding the emitted 4032-byte `sk` recovers EXACTLY the RING-level `(ρ, K, tr, s1, s2, t0)`.

The SPECIFICATION side is `mldsaKeygenRing` — `H` / `ExpandA` / `ExpandS` / `NTT` / matvec / `Power2Round`
over `R_q` (FIPS 204 Alg 6 steps 1–5) — NOT the byte implementation restated. The two sides are related
through the genuine codec inverses (`unpackBits ∘ packBits`, the `BitPack` sign map) composed with the
per-coefficient bounds proved over the `Id.run do` loops: `t1 < 2¹⁰` and `t0 ∈ (−2^{d−1}, 2^{d−1}]` from
`Power2Round`, `s1`/`s2` ∈ `[−η, η]` from the `RejBoundedPoly` rejection invariant. The ML-DSA mirror of
`MlKemKeygenRefine.kpkeKeyGen_refines_ring`. -/
theorem mldsaKeygen_refines_ring (xi : List UInt8) (hS : ExpandSSized xi) :
    pkDecode (mldsaKeygenInternal xi).1 = ((mldsaKeygenRing xi).rho, (mldsaKeygenRing xi).t1)
    ∧ skDecode (mldsaKeygenInternal xi).2 =
        ((mldsaKeygenRing xi).rho, (mldsaKeygenRing xi).kk, trOf xi,
         (mldsaKeygenRing xi).s1, (mldsaKeygenRing xi).s2, (mldsaKeygenRing xi).t0) := by
  refine ⟨mldsaKeygen_pk_refines_ring xi, ?_⟩
  rw [bridge_sk]
  exact skDecode_skEncode _ _ _ _ _ _
    (by rw [ring_rho]; exact rhoOf_length xi)
    (by rw [ring_kk]; exact kkOf_length xi)
    (trOf_length xi)
    (ring_s1_size xi) (ring_s2_size xi) (ring_t0_size xi)
    (fun i hi => by rw [ring_s1]; exact hS.1 i hi)
    (fun i hi => by rw [ring_s2]; exact hS.2 i hi)
    (ring_t0_poly_size xi)
    (ring_s1_range xi hS) (ring_s2_range xi hS) (ring_t0_range xi)

/-! ## §14 — NON-VACUITY of the named leg, and the trusted base.

`ExpandSSized` is not a vacuous hypothesis: it HOLDS on a concrete seed (`native_decide` on the real
`SHAKE-256`-driven sampler), so `mldsaKeygen_refines_ring` genuinely fires. The witness is the ONLY
`native_decide` here and is deliberately kept out of every `∀`-theorem's trusted base. -/

/-- **Non-vacuity**: the `RejBoundedPoly` budget really does suffice — `ExpandSSized` holds on the
all-zero 32-byte seed, so the refinement's one hypothesis is satisfiable and the theorem fires. -/
theorem expandS_sized_witness : ExpandSSized (List.replicate 32 (0 : UInt8)) := by
  unfold ExpandSSized
  native_decide

#print axioms squeeze_length
#print axioms shake256_length
#print axioms bDecode_bEncode
#print axioms power2round_t1_lt
#print axioms power2round_t0_range
#print axioms rejBoundedPoly_range
#print axioms unpackEta_packEta
#print axioms unpackT0_packT0
#print axioms skDecode_skEncode
#print axioms mldsaKeygen_pk_refines_ring
#print axioms mldsaKeygen_refines_ring
#print axioms expandS_sized_witness

#assert_axioms squeeze_length
#assert_axioms rejBoundedPoly_range
#assert_axioms power2round_t1_lt
#assert_axioms power2round_t0_range
#assert_axioms unpackEta_packEta
#assert_axioms unpackT0_packT0
#assert_axioms skDecode_skEncode
#assert_axioms mldsaKeygen_pk_refines_ring
#assert_axioms mldsaKeygen_refines_ring

end Dregg2.Crypto.MlDsaKeygenRefine
