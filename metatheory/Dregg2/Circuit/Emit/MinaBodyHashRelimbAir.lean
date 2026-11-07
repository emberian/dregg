/-
# `Dregg2.Circuit.Emit.MinaBodyHashRelimbAir` — ⚑⚑ **TIE 2 STOPS BEING ARITHMETICALLY
INEXPRESSIBLE.** The bit-level re-limbing between thirty-two 8-bit limbs and nine 29-bit lanes.

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this is a **Lean-authored AIR**. `relimbDesc` is
`EffectLower.lowerTiedAir` applied to the `EffectAir` source `relimbAir` (§3). There is **no
hand-written `VmConstraint2` in this file** and Rust authors nothing; Rust proves the artifact.

## ⚑⚑ THE ARITHMETIC THIS EXISTS TO GET AROUND

The body-hash tie relates thirty-two 8-bit limbs (`dregg-pasta-fp-chainlink::v1`'s squeezed
outgoing lane) to nine 29-bit `Faithful9` lanes (`dregg-mina-lightclient-link::v1`'s `BODYHASH`).
Written directly, `Σ_{k<32} 2^(8k)·limb_k = Σ_{l<9} 2^(29l)·lane_l` carries coefficients to `2^248`
against BabyBear's `p = 2^31 − 2^27 + 1`, so it wraps. **That gate does not exist and this file does
not emit one** — a direct byte↔lane identity is still not a BabyBear linear gate.

What this descriptor does instead is refuse to spell the tie as a relation between two blocks. Both
spellings are read off ONE boolean bit block, so the largest coefficient anywhere is `2^28` (a lane
gate) or `2^7` (a byte gate), and the identity that ties them is not a gate at all but a REGROUPING
theorem over that block (`the_two_spellings_denote_one_value`). Each END of the tie is then an
elementwise pin list, which is what `SeamSpec` can express.

## ⚑ THE SHAPE, AND WHY IT IS 254 BITS AND NOT 256

    col   0 .. 253      BIT j     bit `j` of the value, LSB-first
    col 254 .. 285      BYTE i    Σ_{t<w_i} 2^t · BIT(8i + t)     — coefficients top out at 2^7
    col 286 .. 294      LANE l    Σ_{t<v_l} 2^t · BIT(29l + t)    — coefficients top out at 2^28

    PI  0 ..  31        BYTE i    the chain's spelling  (`dregg-pasta-fp-chainlink::v1`, out lane 0)
    PI 32 ..  40        LANE l    the link's spelling   (`dregg-mina-lightclient-link::v1`, BODYHASH)

⚑⚑ **254, BECAUSE THAT IS WHAT THE LINK'S CANONICALITY GATE MEANS.**
`LightClientMinaAir.MINA_TOP_LANE_BITS` is **22, not the encoder's 24**, and its own docblock says
why: *"`8 · 29 = 232` and `22 + 232 = 254`, so `lane 8 < 2^22` is EXACTLY `value < 2^254`, which is
EXACTLY canonicality (`2^254 < pN`). At 24 the nonet is merely a well-formed 32-byte string and the
`+pN`-shifted anchor passes."* A 256-column bit block would hand the seam two columns the link's
own gate refuses to read, so `byteWidth 31 = 6` and `laneWidth 8 = 22` and the two partitions cover
the SAME 254 bits: `31·8 + 6 = 254 = 8·29 + 22`.

⚑ That makes the descriptor the canonicality gate for the weld rather than a party to it: **there
is no column in which a 255th bit could live**, so the phantom is unrepresentable rather than
gated — the same refusal `MinaBodyPreimageBitsAir`'s `⌈W_e/8⌉` allocation makes one rung down. ⚠ And
say what it costs: the byte seam is UNSATISFIABLE against a chain limb block denoting a value in
`[2^254, pN)`. Those exist (`pN − 2^254 ≈ 2^65.3`, so a fraction `≈ 2^-189` of `Fp`); a body hash in
that window would refuse rather than mis-weld, which is the direction a refusal should fail in.

## ⚑ THE PRICE — LOOKUP-FREE, AND THE MEASUREMENT IS THE POINT

`MinaBodyPreimageBitsAir` paid **1 216 eight-bit range lookups** for its 38 felt-level `.limbs`
legs and its committed width went `3 899 → 6 331`, 1.62×. **This descriptor declares NO table and
emits NO lookup** (`the_relimbing_has_no_lookup_bill`): a booleanity assertion is a degree-2 window
gate and a composition gate is affine, so `MainLayout::build` appends no nibble aux block and the
committed width IS the declared width. The bound on a byte column is not a bus query — it is the
count of bit columns under it (`the_gates_bound_their_own_columns`).

⚠ Said as the arithmetic rather than as a slogan: `BYTE i < 2^8` and `LANE l < 2^29` hold because
there are `w_i` resp. `v_l` boolean summands, so the descriptor's own booleanity legs are the range
gate. That is why the fix specified lookup-free, and it is why it stays that way.

## ⚑ WHAT IT BUYS, AND THE ALIAS THAT SHOWS BOOLEANITY IS LOAD-BEARING

Two theorems, and they need DIFFERENT hypotheses — which is the whole content:

  * **`the_two_spellings_denote_one_value`** — no hypothesis at all. The 32-byte reading and the
    9-lane reading of the same bit columns are the same integer. This is a REGROUPING, not a gate.
  * **`the_relimbing_is_injective`** — needs booleanity, and
    `the_booleanity_hypothesis_is_load_bearing` exhibits what follows when it is dropped:

        bits A: column 28 carries 2      bytes = […, byte 3 = 32, …]   lanes = [2^29, 0, 0, …]
        bits B: column 29 carries 1      bytes = […, byte 3 = 32, …]   lanes = [0,    1, 0, …]

    **Bit columns 28 and 29 are both inside byte 3 and straddle the lane 0 / lane 1 boundary** —
    the byte partition and the lane partition do not refine one another, because `29 % 8 ≠ 0`. So
    without booleanity: *the same thirty-two chain limbs, the same `state_body_hash`, the same
    fold root, every link honest — and the light client's `BODYHASH` nonet is a different felt.*
    That is `Bridge.MinaPackInjective.the_range_hypothesis_is_load_bearing`'s alias one rail down,
    and it is the reason this descriptor gates bits instead of welding bytes to lanes directly.

## ⚑ WHAT THIS BREAKS (flag day, stated so it is findable)

**2026-08-10 — A NEW DESCRIPTOR, `dregg-mina-bodyhash-relimb::v1`.** Nothing existing changes
shape. It emits `circuit/descriptors/by-name/dregg-mina-bodyhash-relimb-v1.json`, mints a VK, and
takes `EmitByName.byNameDescriptors_length` from 131 to 132 (rows and pin are one atom). No VK
rotates, nothing re-genesises, and `PROVENANCE.json` gains no row that this file stamps.

⚠ **AND IT GIVES `MinaSeams.bodyHashPort` A SECOND COVER.** That port was `WeldCover`-only —
REFUSAL 16d, an executor comparison. `MinaBodyHashRelimbSeams.bodyHashPortCovered` adds a
`CoveredPort` over a registered seam; the `WeldCover` stays until a fold applies the seam, because
until then REFUSAL 16d is what a node runs.

## Import line for the root: `import Dregg2.Circuit.Emit.MinaBodyHashRelimbAir`
-/
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Circuit.Emit.PastaFieldSound
import Dregg2.Circuit.Emit.SeamSpec
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.MinaBodyHashRelimbAir

open Dregg2.Circuit (Assignment Expr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB limbAt)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg PiPinLeg WindowLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)

set_option autoImplicit false
set_option maxRecDepth 200000
-- ⚑ 336 legs through `lowerAir`, and the `rfl` shape pins below reduce the whole emitted list.
set_option maxHeartbeats 1600000

/-! ## §1 — ⚑ THE TWO PARTITIONS OF ONE 254-BIT BLOCK. -/

/-- The bit block's width. ⚑ `254`, not `256` — the link's `MINA_TOP_LANE_BITS = 22` reading, and
`31·8 + 6 = 254 = 8·29 + 22`. -/
def NBIT : Nat := 254

/-- Byte columns — the CHAIN's spelling, `SK` of them. -/
def NBYTE : Nat := SK

/-- Lane columns — the LINK's spelling. -/
def NLANE : Nat := 9

/-- ⚑ **The link's lane width, `MINA_LANE_BITS`.** Restated locally rather than imported, exactly
as `LightClientMinaAir.RANGE_W_TID_BASE` is restated in its own consumers: importing the link AIR
into an EMIT cone makes every exe in it evaluate that AIR at initialization. ⚠ Two constants for
one fact is the twin this repo forbids, so the reconciliation is FORCED rather than remembered —
`MinaBodyHashRelimbSeams.the_lane_widths_are_the_links` is `rfl` against the link's own literals
and goes red the day either moves. -/
def LB : Nat := 29

/-- ⚑ **The link's TOP lane width, `MINA_TOP_LANE_BITS` — 22, and it is the canonicality gate.**
See the header: at 24 the nonet is a well-formed byte string and the `+pN`-shifted anchor passes. -/
def TOP_LB : Nat := 22

/-- How many bits byte `i` holds: eight, except the last, which holds the six that are left. -/
def byteWidth (i : Nat) : Nat := if i + 1 < NBYTE then SB else NBIT - SB * (NBYTE - 1)

/-- How many bits lane `l` holds: `LB`, except the top, which holds `TOP_LB`. -/
def laneWidth (l : Nat) : Nat := if l + 1 < NLANE then LB else TOP_LB

/-- The stream-bit offset lane `l` starts at. -/
def laneStart (l : Nat) : Nat := LB * l

/-- ⚑⚑ **THE TWO PARTITIONS COVER THE SAME 254 BITS, WITH NOTHING LEFT OVER AND NOTHING TWICE.**
Both sums are `NBIT`; the byte runs start at `SB · i` and the lane runs at `LB · l`, each starting
where its predecessor ended. ⚠ Without this the "two spellings" are two DIFFERENT windows and the
regrouping theorem below is about a coincidence. -/
theorem the_two_partitions_cover_the_same_bits :
    ((List.range NBYTE).map byteWidth).foldl (· + ·) 0 = NBIT
      ∧ ((List.range NLANE).map laneWidth).foldl (· + ·) 0 = NBIT
      ∧ (∀ i < NBYTE, SB * i + byteWidth i = SB * (i + 1) ∨ i + 1 = NBYTE)
      ∧ (∀ l < NLANE, laneStart l + laneWidth l = laneStart (l + 1) ∨ l + 1 = NLANE)
      ∧ byteWidth (NBYTE - 1) = 6 ∧ laneWidth (NLANE - 1) = TOP_LB
      ∧ SB * (NBYTE - 1) + 6 = NBIT ∧ LB * (NLANE - 1) + TOP_LB = NBIT := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑⚑ **AND THEY DO NOT REFINE ONE ANOTHER — the fact the whole file turns on.** `LB % SB ≠ 0`,
so seven lane boundaries fall strictly INSIDE a byte. Those seven interior boundaries are exactly
where the alias of §6 lives; a partition pair that refined would have no alias and would also need
no bit block. -/
theorem the_lane_boundaries_fall_inside_bytes :
    LB % SB ≠ 0
      ∧ ((List.range NLANE).filter fun l => 0 < l && decide (laneStart l % SB ≠ 0)) = [1,2,3,4,5,6,7]
      ∧ laneStart 1 = 29 ∧ laneStart 1 / SB = 3 ∧ (NBIT - 1) / SB = NBYTE - 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ### §1a — the index facts every proof below leans on, named once.

`byteWidth` and `laneWidth` are `if`s, so any goal mentioning them needs a `split` before `omega`.
Doing that once here keeps it out of a dozen call sites, where a stuck `omega` on an unsplit `if`
reads like a missing lemma. -/

theorem byteWidth_eq_SB {i : Nat} (hi : i + 1 < NBYTE) : byteWidth i = SB := by
  unfold byteWidth; simp [hi]

theorem laneWidth_eq_LB {l : Nat} (hl : l + 1 < NLANE) : laneWidth l = LB := by
  unfold laneWidth; simp [hl]

theorem byteWidth_top : byteWidth (NBYTE - 1) = 6 := by native_decide
theorem laneWidth_top : laneWidth (NLANE - 1) = TOP_LB := by native_decide

/-- Byte `i`'s run stays inside the bit block. -/
theorem byte_run_inside {i t : Nat} (hi : i < NBYTE) (ht : t < byteWidth i) : SB * i + t < NBIT := by
  have h : byteWidth i = if i + 1 < NBYTE then SB else NBIT - SB * (NBYTE - 1) := rfl
  rw [h] at ht
  unfold NBYTE SK SB NBIT at *
  split at ht <;> omega

/-- Lane `l`'s run stays inside the bit block. -/
theorem lane_run_inside {l t : Nat} (hl : l < NLANE) (ht : t < laneWidth l) :
    laneStart l + t < NBIT := by
  have h : laneWidth l = if l + 1 < NLANE then LB else TOP_LB := rfl
  rw [h] at ht
  unfold laneStart NLANE LB TOP_LB NBIT at *
  split at ht <;> omega

/-- ⚑ **EVERY BIT LIES IN EXACTLY ONE BYTE'S RUN.** The statement that makes the byte partition a
partition at the INDEX level — the injectivity proof walks bit `j` back to byte `j / SB` and needs
`j % SB` to be inside that byte's width, which for the ragged top byte is `6` and not `8`. -/
theorem bit_in_its_byte {j : Nat} (hj : j < NBIT) : j % SB < byteWidth (j / SB) ∧ j / SB < NBYTE := by
  have h : byteWidth (j / SB) = if j / SB + 1 < NBYTE then SB else NBIT - SB * (NBYTE - 1) := rfl
  rw [h]
  unfold NBYTE SK SB NBIT at *
  refine ⟨?_, by omega⟩
  split <;> omega

/-! ## §2 — the column layout and the PI slots. -/

/-- **`BIT j`** — bit `j` of the re-limbed value, LSB-first. -/
def BIT (j : Nat) : Nat := j

/-- **`BYTE i`** — the chain's `i`-th base-256 limb, the same encoding `PastaFieldSound.limbAt`
indexes and `MinaStateBodyHashChain`'s outgoing lane 0 publishes. -/
def BYTE (i : Nat) : Nat := NBIT + i

/-- **`LANE l`** — the link's `l`-th base-`2^29` lane, the same encoding
`LightClientMinaAir.stateValue` reads and `LightClientMinaLinkAir.BODYHASH` publishes. -/
def LANE (l : Nat) : Nat := NBIT + NBYTE + l

def RELIMB_WIDTH : Nat := NBIT + NBYTE + NLANE

/-- PI slot of `BYTE i` — slots `[0, 32)`, the CHAIN-facing half of the claim. -/
def PI_BYTE (i : Nat) : Nat := i

/-- PI slot of `LANE l` — slots `[32, 41)`, the LINK-facing half of the claim. -/
def PI_LANE (l : Nat) : Nat := NBYTE + l

def RELIMB_PI_COUNT : Nat := NBYTE + NLANE

theorem the_layout_is_wellformed :
    RELIMB_WIDTH = 295 ∧ RELIMB_PI_COUNT = 41
      ∧ BIT 0 = 0 ∧ BIT (NBIT - 1) = 253
      ∧ BYTE 0 = 254 ∧ BYTE 31 = 285
      ∧ LANE 0 = 286 ∧ LANE 8 = 294
      ∧ BYTE 31 < RELIMB_WIDTH ∧ LANE 8 < RELIMB_WIDTH
      ∧ PI_BYTE 31 < RELIMB_PI_COUNT ∧ PI_LANE 8 < RELIMB_PI_COUNT := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## §3 — ⚑ THE BIT-RUN ARITHMETIC. The vocabulary both spellings are read in.

One definition — `bitSumAt row base n`, the value of `n` bit columns starting at `base` — and one
splitting lemma. Everything downstream is those two: the byte gates, the lane gates, the regrouping
that ties them, and the injectivity that makes the tie carry a value. -/

/-- ⚑ **`Σ_{t<n} 2^t · BIT(base + t)`** — the value a run of `n` bit columns denotes. -/
def bitSumAt (row : Nat → ℤ) (base n : Nat) : ℤ :=
  ((List.range n).map (fun t => (2 : ℤ) ^ t * row (BIT (base + t)))).sum

theorem bitSumAt_zero (row : Nat → ℤ) (base : Nat) : bitSumAt row base 0 = 0 := rfl

/-- Peel the TOP bit of a run. -/
theorem bitSumAt_succ (row : Nat → ℤ) (base n : Nat) :
    bitSumAt row base (n + 1) = bitSumAt row base n + (2 : ℤ) ^ n * row (BIT (base + n)) := by
  unfold bitSumAt
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

/-- ⚑⚑ **THE SPLITTING LEMMA** — a run of `m + n` bits is its low `m` plus `2^m` times the `n`
above them. This is the ONE fact both regroupings are built from, and it is why a partition of the
bit block into runs of ANY widths recomposes to the same value. -/
theorem bitSumAt_split (row : Nat → ℤ) (base m n : Nat) :
    bitSumAt row base (m + n) = bitSumAt row base m + (2 : ℤ) ^ m * bitSumAt row (base + m) n := by
  induction n with
  | zero => simp [bitSumAt_zero]
  | succ k ih =>
      have hidx : base + m + k = base + (m + k) := by omega
      rw [← Nat.add_assoc, bitSumAt_succ, ih, bitSumAt_succ, hidx]
      ring

/-- Pointwise bit agreement transports a run's value. -/
theorem bitSumAt_congr {f g : Nat → ℤ} {base n : Nat} (h : ∀ t, t < n → f (BIT (base + t)) = g (BIT (base + t))) :
    bitSumAt f base n = bitSumAt g base n := by
  unfold bitSumAt
  refine congrArg List.sum (List.map_congr_left ?_)
  intro t ht
  rw [h t (List.mem_range.mp ht)]

/-- ⚑ **A RUN OF BOOLEAN COLUMNS IS BELOW `2^n`, AND NON-NEGATIVE.** This is the range gate, and it
is the descriptor's own booleanity legs rather than a bus query — the reason this rung is
lookup-free. -/
theorem bitSumAt_bounds {row : Nat → ℤ} {base : Nat} :
    ∀ n, (∀ t, t < n → row (BIT (base + t)) = 0 ∨ row (BIT (base + t)) = 1) →
      0 ≤ bitSumAt row base n ∧ bitSumAt row base n < (2 : ℤ) ^ n := by
  intro n
  induction n with
  | zero => intro _; rw [bitSumAt_zero]; norm_num
  | succ k ih =>
      intro hb
      obtain ⟨hlo, hhi⟩ := ih (fun t ht => hb t (Nat.lt_succ_of_lt ht))
      have hpow : (0 : ℤ) < 2 ^ k := by positivity
      have hsucc : (2 : ℤ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      rw [bitSumAt_succ]
      rcases hb k (Nat.lt_succ_self k) with h0 | h1
      · rw [h0, mul_zero, add_zero]
        exact ⟨hlo, by rw [hsucc]; linarith⟩
      · rw [h1, mul_one]
        exact ⟨by linarith, by rw [hsucc]; linarith⟩

/-- ⚑⚑⚑ **BIT-RUN INJECTIVITY.** Two runs of BOOLEAN columns with the same value have the same
columns. ⚠ The booleanity hypothesis is the whole content — §6 exhibits the alias that appears the
moment it is dropped. -/
theorem bitSumAt_inj {f g : Nat → ℤ} {base : Nat} :
    ∀ n, (∀ t, t < n → f (BIT (base + t)) = 0 ∨ f (BIT (base + t)) = 1) →
      (∀ t, t < n → g (BIT (base + t)) = 0 ∨ g (BIT (base + t)) = 1) →
      bitSumAt f base n = bitSumAt g base n →
      ∀ t, t < n → f (BIT (base + t)) = g (BIT (base + t)) := by
  intro n
  induction n with
  | zero => intro _ _ _ t ht; exact absurd ht (Nat.not_lt_zero t)
  | succ k ih =>
      intro hf hg h t ht
      have hflo := (bitSumAt_bounds (row := f) (base := base) k
        (fun s hs => hf s (Nat.lt_succ_of_lt hs)))
      have hglo := (bitSumAt_bounds (row := g) (base := base) k
        (fun s hs => hg s (Nat.lt_succ_of_lt hs)))
      have hfk := hf k (Nat.lt_succ_self k)
      have hgk := hg k (Nat.lt_succ_self k)
      rw [bitSumAt_succ, bitSumAt_succ] at h
      -- the TOP column is forced: a boolean `1` there puts the run at or above `2^k`, a `0` below
      have htop : f (BIT (base + k)) = g (BIT (base + k)) := by
        rcases hfk with h0 | h1
        · rcases hgk with h0' | h1'
          · rw [h0, h0']
          · exfalso
            rw [h0, mul_zero, add_zero, h1', mul_one] at h
            linarith [hflo.1, hflo.2, hglo.1, hglo.2]
        · rcases hgk with h0' | h1'
          · exfalso
            rw [h1, mul_one, h0', mul_zero, add_zero] at h
            linarith [hflo.1, hflo.2, hglo.1, hglo.2]
          · rw [h1, h1']
      have hrest : bitSumAt f base k = bitSumAt g base k := by
        rw [htop] at h; linarith
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | heq
      · exact ih (fun s hs => hf s (Nat.lt_succ_of_lt hs))
          (fun s hs => hg s (Nat.lt_succ_of_lt hs)) hrest t hlt
      · rw [heq]; exact htop

/-! ## §4 — ⚑ THE POSITIONAL READING, at a general digit width.

`Seam.digitsVal` is base-`2^SB` by construction, and the lane spelling is base-`2^LB`. One
width-parameterized fold serves both, and `digitsValW_SB` is the `rfl` that keeps it ONE object
with the seam layer's rather than a parallel encoding. -/

/-- `Σ_{i<n} (2^w)^i · get i`, Horner from the top — the shape `Seam.digitsVal` is written in. -/
def digitsValW (w : Nat) (get : Nat → ℤ) (n : Nat) : ℤ :=
  (List.range n).foldr (fun i acc => acc * (2 ^ w : ℤ) + get i) 0

/-- ⚑ **THE SEAM LAYER'S READING IS THIS ONE AT `w = SB`** — `rfl`, so a value read through
`Seam.Renders`/`Seam.digitsVal` on the chain side and through `digitsValW` here is ONE number. -/
theorem digitsValW_SB (get : Nat → ℤ) (n : Nat) :
    digitsValW SB get n = Dregg2.Circuit.Emit.Seam.digitsVal get n := rfl

private theorem digitsValW_gen (w : Nat) (get : Nat → ℤ) :
    ∀ (n : Nat) (z : ℤ),
      (List.range n).foldr (fun i acc => acc * (2 ^ w : ℤ) + get i) z
        = z * ((2 : ℤ) ^ w) ^ n + digitsValW w get n := by
  intro n
  induction n with
  | zero => intro z; simp [digitsValW]
  | succ k ih =>
      intro z
      have hstep : ∀ y : ℤ, (List.range (k + 1)).foldr (fun i acc => acc * (2 ^ w : ℤ) + get i) y
          = (List.range k).foldr (fun i acc => acc * (2 ^ w : ℤ) + get i)
              (y * (2 ^ w : ℤ) + get k) := by
        intro y
        rw [List.range_succ, List.foldr_append]
        simp
      rw [hstep z, ih (z * (2 ^ w : ℤ) + get k)]
      have hz : digitsValW w get (k + 1)
          = (0 * (2 ^ w : ℤ) + get k) * ((2 : ℤ) ^ w) ^ k + digitsValW w get k := by
        unfold digitsValW
        rw [hstep 0, ih (0 * (2 ^ w : ℤ) + get k)]
        rfl
      rw [hz]
      ring

/-- Peel the TOP digit. -/
theorem digitsValW_succ (w : Nat) (get : Nat → ℤ) (n : Nat) :
    digitsValW w get (n + 1) = digitsValW w get n + ((2 : ℤ) ^ w) ^ n * get n := by
  have hstep : digitsValW w get (n + 1)
      = (List.range n).foldr (fun i acc => acc * (2 ^ w : ℤ) + get i) (0 * (2 ^ w : ℤ) + get n) := by
    unfold digitsValW
    rw [List.range_succ, List.foldr_append]
    simp
  rw [hstep, digitsValW_gen]
  ring

/-- An all-zero digit vector reads as zero, at any width. -/
theorem digitsValW_zero (w n : Nat) : digitsValW w (fun _ => (0 : ℤ)) n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [digitsValW_succ, ih]; ring

theorem digitsValW_congr {w : Nat} {f g : Nat → ℤ} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    digitsValW w f n = digitsValW w g n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [digitsValW_succ, digitsValW_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
        h k (Nat.lt_succ_self k)]

/-- ⚑⚑ **THE UNIFORM REGROUPING** — `n` runs of `w` bits, read positionally at base `2^w`, are the
`w·n` bits read as one run. Proved once and used at BOTH partitions (bytes at `w = 8`, lanes at
`w = 29`); the ragged top run is the ONE extra `bitSumAt_split` each spelling needs. -/
theorem digitsValW_of_runs (row : Nat → ℤ) (w : Nat) :
    ∀ n, digitsValW w (fun i => bitSumAt row (w * i) w) n = bitSumAt row 0 (w * n) := by
  intro n
  induction n with
  | zero => simp [digitsValW, bitSumAt_zero]
  | succ k ih =>
      rw [digitsValW_succ, ih]
      have hmul : w * (k + 1) = w * k + w := by ring
      rw [hmul, bitSumAt_split row 0 (w * k) w, Nat.zero_add, ← pow_mul]

/-! ## §5 — the SOURCE legs. Every one is a window gate; not one is a lookup. -/

open WindowExpr (loc)

/-- ⚑ **THE BOOLEANITY LEG** — `x·(x−1) = 0`, `GateExpr.gBool`'s five-node encoding, at `.all` so a
padding row is pinned too. 254 of them, and together they ARE this descriptor's range gate. -/
def bitBoolLeg (j : Nat) : AirLeg :=
  .window ⟨RowSel.all, Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gBool (.leaf (.loc (BIT j))))⟩

theorem bitBoolLeg_eq (j : Nat) :
    bitBoolLeg j
      = .window ⟨RowSel.all, .mul (loc (BIT j)) (.add (loc (BIT j)) (.const (-1)))⟩ := rfl

/-- The `(coefficient, bit column)` terms of a run: `2^t` against `BIT (base + t)`. -/
def runTerms (base n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun t => (2 ^ t, BIT (base + t))

/-- `Σ cᵢ · BIT colᵢ`, right-folded. -/
def termSum : List (Nat × Nat) → WindowExpr
  | [] => .const 0
  | (c, col) :: rest => .add (.mul (.const (c : ℤ)) (loc col)) (termSum rest)

/-- The value a term list denotes at a row — the gate's OWN right fold. -/
def termValue (row : Nat → ℤ) (ts : List (Nat × Nat)) : ℤ :=
  ts.foldr (fun t acc => (t.1 : ℤ) * row t.2 + acc) 0

private theorem termValue_cons (row : Nat → ℤ) (t : Nat × Nat) (ts : List (Nat × Nat)) :
    termValue row (t :: ts) = (t.1 : ℤ) * row t.2 + termValue row ts := rfl

/-- ⚑ **THE GATE'S FOLD IS `bitSumAt`** — so the row predicate of §7 speaks the EMITTED leg's
arithmetic and not a parallel encoding of it. ⚠ Without this the whole file could be true of an
object the descriptor does not constrain. -/
theorem termValue_runTerms (row : Nat → ℤ) (base : Nat) :
    ∀ n, termValue row (runTerms base n) = bitSumAt row base n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [bitSumAt_succ, ← ih]
      unfold runTerms termValue
      rw [List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil, List.foldr_append, List.foldr_cons, List.foldr_nil]
      induction (List.range k) with
      | nil => simp
      | cons a as iha => simp only [List.map_cons, List.foldr_cons, iha]; ring

/-- The bit columns byte `i` composes. -/
def byteTerms (i : Nat) : List (Nat × Nat) := runTerms (SB * i) (byteWidth i)

/-- The bit columns lane `l` composes. -/
def laneTerms (l : Nat) : List (Nat × Nat) := runTerms (laneStart l) (laneWidth l)

/-- ⚑ **THE BYTE LEG** — `BYTE i − Σ 2^t · BIT(8i + t) = 0`. Affine, and its largest coefficient is
`2^7 = 128`. -/
def byteLeg (i : Nat) : AirLeg :=
  .window ⟨RowSel.all, .add (loc (BYTE i)) (.mul (.const (-1)) (termSum (byteTerms i)))⟩

/-- ⚑ **THE LANE LEG** — `LANE l − Σ 2^t · BIT(29l + t) = 0`. Affine, and its largest coefficient
is `2^28 = 268 435 456`, comfortably inside BabyBear (`p = 2^31 − 2^27 + 1 = 2 013 265 921`). -/
def laneLeg (l : Nat) : AirLeg :=
  .window ⟨RowSel.all, .add (loc (LANE l)) (.mul (.const (-1)) (termSum (laneTerms l)))⟩

def bytePin (i : Nat) : AirLeg := .pin ⟨VmRow.first, BYTE i, PI_BYTE i⟩
def lanePin (l : Nat) : AirLeg := .pin ⟨VmRow.first, LANE l, PI_LANE l⟩

/-- ⚑⚑ **EVERY COEFFICIENT IS IN-FIELD, AND THAT IS THE WHOLE BLOCKER REMOVED.** Decided on the
term lists the legs are built from: no byte gate carries a coefficient above `2^7` and no lane gate
above `2^28`, against BabyBear's `2 013 265 921`. ⚠ The direct byte↔lane identity this replaces
carries `2^248`; that gate is still not expressible and this file does not emit one. -/
theorem the_gate_coefficients_are_in_field :
    ((List.range NBYTE).all fun i => (byteTerms i).all fun t => decide (t.1 ≤ 2 ^ 7)) = true
      ∧ ((List.range NLANE).all fun l => (laneTerms l).all fun t => decide (t.1 ≤ 2 ^ 28)) = true
      ∧ 2 ^ 28 < 2013265921 ∧ 2 ^ 29 < 2013265921
      ∧ ¬ (2 ^ 248 < 2013265921) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **NO PUBLISHED COLUMN IS INERT.** Every byte and every lane has at least one bit column under
it, so its gate names TWO columns and the emitted `pi_binding`'s column sits in a component larger
than itself — `LightClientAnchorConnectivity.decorativeAnchors = []` decided on the SOURCE. -/
theorem no_published_column_is_inert :
    ((List.range NBYTE).all fun i => !(byteTerms i).isEmpty) = true
      ∧ ((List.range NLANE).all fun l => !(laneTerms l).isEmpty) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- ⚑ **THE SOURCE.** 32 byte gates, 9 lane gates, 254 booleanity gates, then the 41 pins.

⚠ The ORDER is not cosmetic: `EffectAir.pinsTied` resolves each pin by scanning the leg list from
the front, so putting the two DERIVING families first is what keeps the tie verdict a kernel
`decide` instead of a scan behind 254 booleanity legs. -/
def relimbAir : EffectAir :=
  { tables := []
  , legs :=
      ((List.range NBYTE).map byteLeg)
        ++ ((List.range NLANE).map laneLeg)
        ++ ((List.range NBIT).map bitBoolLeg)
        ++ ((List.range NBYTE).map bytePin)
        ++ ((List.range NLANE).map lanePin) }

theorem relimbAir_leg_count : relimbAir.legs.length = 336 := by native_decide

theorem relimbAir_mainRailOk : relimbAir.mainRailOk = true := by rfl

theorem relimbAir_pinsFit : relimbAir.pinsFit RELIMB_PI_COUNT = true := by rfl

theorem relimbAir_pinsTied : relimbAir.pinsTied = true := by decide

/-- ⚑⚑⚑ **THE LOOKUP BILL IS ZERO, AND THAT IS THE SPECIFICATION MET.** The fix was specified
*"all in-field, lookup-free"*; this is that, decided on the SOURCE. ⚠ Its sibling one rung down
(`MinaBodyPreimageBitsAir`) pays 1 216 eight-bit lookups for its felt gate and its committed width
is 1.62× its declared — a bound on a WHOLE felt has to be a bus query. A bound on a byte or a lane
does not, because the bits under it are already gated. -/
theorem the_relimbing_has_no_lookup_bill :
    relimbAir.limbsCount = 0
      ∧ relimbAir.totalRangeLookups = 0
      ∧ relimbAir.ranges = []
      ∧ relimbAir.tables = [] := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;> rfl

/-- ⚑ **THE TIED SOURCE** — every published column is derived by another leg, carried in the type.
Both verdicts are SUPPLIED so the tree does not pay for them twice. -/
def relimbTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := relimbAir
  ok   := relimbAir_mainRailOk
  tied := relimbAir_pinsTied

/-- **`relimbDesc` — COMPILER OUTPUT.** -/
def relimbDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-bodyhash-relimb::v1" RELIMB_WIDTH RELIMB_PI_COUNT [] relimbTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — stated in the SOURCE's vocabulary
and never mentioning the lowering, so it is not `P → P`. -/
theorem relimbDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines relimbDesc [] relimbAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-bodyhash-relimb::v1" RELIMB_WIDTH RELIMB_PI_COUNT [] relimbTiedAir).property

theorem relimbDesc_name : relimbDesc.name = "dregg-mina-bodyhash-relimb::v1" := rfl
theorem relimbDesc_width : relimbDesc.traceWidth = 295 := rfl
theorem relimbDesc_piCount : relimbDesc.piCount = 41 := rfl
theorem relimbDesc_tables : relimbDesc.tables = [] := rfl
theorem relimbDesc_ranges : relimbDesc.ranges = [] := rfl
theorem relimbDesc_hashSites : relimbDesc.hashSites = [] := rfl
theorem relimbDesc_constraint_count : relimbDesc.constraints.length = 336 := by native_decide

/-- ⚑⚑⚑ **THE COMMITTED WIDTH IS THE DECLARED WIDTH, DECIDED ON THE COMPILER'S OUTPUT.**
`MainLayout::build` appends `decomp_cols(bits)` columns per RANGE lookup and `2 · SUBMASK_BITS` per
submask lookup; this descriptor emits ZERO `lookup` constraints, so it appends nothing and the
committed width is 295 — **295 declared → 295 committed, 1.00×**.
`circuit/tests/mina_bodyhash_relimb_proves.rs` re-derives the same number from `decomp_cols_pub` on
the emitted bytes and reports the LDE domain beside it. -/
theorem the_lookup_constraint_count_is_zero :
    (relimbDesc.constraints.filter fun c =>
      match c with | .lookup _ => true | _ => false).length = 0
    ∧ relimbDesc.tables = []
    ∧ relimbDesc.traceWidth = 295 := by
  refine ⟨?_, rfl, rfl⟩
  native_decide

/-! ### §5a — decided on the emitted bytes. -/

def readsCell : WindowExpr → Bool
  | .loc _ => true
  | .nxt _ => true
  | .const _ => false
  | .add a b => readsCell a || readsCell b
  | .mul a b => readsCell a || readsCell b

def cellCols : WindowExpr → List Nat
  | .loc c => [c]
  | .nxt c => [c]
  | .const _ => []
  | .add a b => cellCols a ++ cellCols b
  | .mul a b => cellCols a ++ cellCols b

def prodCols : WindowExpr → List Nat
  | .loc _ => []
  | .nxt _ => []
  | .const _ => []
  | .add a b => prodCols a ++ prodCols b
  | .mul a b =>
      (if readsCell a && readsCell b then cellCols a ++ cellCols b else []) ++
        prodCols a ++ prodCols b

def constraintProdCols : VmConstraint2 → List Nat
  | .windowGate w => prodCols w.body
  | _ => []

/-- ⚑ **EVERY TWO-SIDED PRODUCT IS A BOOLEANITY PIN ON ONE COLUMN.** The byte and lane legs are
affine, so the only columns under a product are the bit columns squaring themselves. A descriptor
that had welded bytes to lanes directly would put two different indices under one coefficient; none
does. -/
theorem relimb_products_are_only_the_bits :
    (relimbDesc.constraints.all fun c =>
      (constraintProdCols c).eraseDups.length ≤ 1) = true := by native_decide

/-! ## §6 — ⚑⚑⚑ THE ROW PREDICATE, THE REGROUPING, THE INJECTIVITY, AND THE ALIAS. -/

/-- ⚑ **`relimbRowOk` — the emitted constraint set's content, as a verdict.** FIVE conjuncts, one
per leg family: booleanity on every bit column, each byte the exact run its bits compose, each lane
the exact run ITS bits compose, and both blocks published. -/
def relimbRowOk (row pub : Nat → ℤ) : Prop :=
  (∀ j < NBIT, row (BIT j) * (row (BIT j) - 1) = 0)
  ∧ (∀ i < NBYTE, row (BYTE i) = bitSumAt row (SB * i) (byteWidth i))
  ∧ (∀ l < NLANE, row (LANE l) = bitSumAt row (laneStart l) (laneWidth l))
  ∧ (∀ i < NBYTE, pub (PI_BYTE i) = row (BYTE i))
  ∧ (∀ l < NLANE, pub (PI_LANE l) = row (LANE l))

theorem the_row_gates_force_boolean_bits {row pub : Nat → ℤ} (h : relimbRowOk row pub) :
    ∀ j, j < NBIT → row (BIT j) = 0 ∨ row (BIT j) = 1 := by
  intro j hj
  rcases mul_eq_zero.mp (h.1 j hj) with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-- The BYTE spelling of a claim, read positionally base `2^SB`. -/
def claimByteValue (pub : Nat → ℤ) : ℤ := digitsValW SB (fun i => pub (PI_BYTE i)) NBYTE

/-- The LANE spelling of a claim, read positionally base `2^LB`. -/
def claimLaneValue (pub : Nat → ℤ) : ℤ := digitsValW LB (fun l => pub (PI_LANE l)) NLANE

private theorem byte_reading_is_the_bit_block {row pub : Nat → ℤ} (h : relimbRowOk row pub) :
    claimByteValue pub = bitSumAt row 0 NBIT := by
  unfold claimByteValue
  -- peel the ragged top byte, then apply the uniform regrouping to the 31 below it
  have htop : NBYTE = 31 + 1 := rfl
  rw [htop, digitsValW_succ]
  have hlow : digitsValW SB (fun i => pub (PI_BYTE i)) 31
      = digitsValW SB (fun i => bitSumAt row (SB * i) SB) 31 := by
    refine digitsValW_congr (fun i hi => ?_)
    rw [h.2.2.2.1 i (by unfold NBYTE SK; omega), h.2.1 i (by unfold NBYTE SK; omega),
      byteWidth_eq_SB (by unfold NBYTE SK; omega)]
  rw [hlow, digitsValW_of_runs row SB 31]
  have htopval : pub (PI_BYTE 31) = bitSumAt row (SB * 31) 6 := by
    rw [h.2.2.2.1 31 (by decide), h.2.1 31 (by decide)]
    rfl
  rw [htopval]
  have hsplit := bitSumAt_split row 0 (SB * 31) 6
  rw [Nat.zero_add] at hsplit
  have hsum : SB * 31 + 6 = NBIT := by decide
  rw [hsum] at hsplit
  rw [hsplit, ← pow_mul]

private theorem lane_reading_is_the_bit_block {row pub : Nat → ℤ} (h : relimbRowOk row pub) :
    claimLaneValue pub = bitSumAt row 0 NBIT := by
  unfold claimLaneValue
  have htop : NLANE = 8 + 1 := rfl
  rw [htop, digitsValW_succ]
  have hlow : digitsValW LB (fun l => pub (PI_LANE l)) 8
      = digitsValW LB (fun l => bitSumAt row (LB * l) LB) 8 := by
    refine digitsValW_congr (fun l hl => ?_)
    rw [h.2.2.2.2 l (by unfold NLANE; omega), h.2.2.1 l (by unfold NLANE; omega),
      laneWidth_eq_LB (by unfold NLANE; omega)]
    rfl
  rw [hlow, digitsValW_of_runs row LB 8]
  have htopval : pub (PI_LANE 8) = bitSumAt row (LB * 8) TOP_LB := by
    rw [h.2.2.2.2 8 (by decide), h.2.2.1 8 (by decide)]
    rfl
  rw [htopval]
  have hsplit := bitSumAt_split row 0 (LB * 8) TOP_LB
  rw [Nat.zero_add] at hsplit
  have hsum : LB * 8 + TOP_LB = NBIT := by decide
  rw [hsum] at hsplit
  rw [hsplit, ← pow_mul]

/-- ⚑⚑⚑ **THE RE-LIMBING, AS A THEOREM — AND IT NEEDS NO HYPOTHESIS AT ALL.** A row this
descriptor accepts publishes a 32-byte block and a 9-lane block that denote the SAME integer. This
is the sentence the tie needs and the one a BabyBear linear gate could not carry: the identity is a
REGROUPING of one bit vector, not a relation between two blocks, so no coefficient above `2^28`
ever appears.

⚠ Booleanity is NOT among the hypotheses, deliberately. It is not what makes the two readings
agree — it is what makes each reading DETERMINE the bits, which is the next theorem, and §6a is the
alias that shows the difference is not cosmetic. -/
theorem the_two_spellings_denote_one_value {row pub : Nat → ℤ} (h : relimbRowOk row pub) :
    claimByteValue pub = claimLaneValue pub := by
  rw [byte_reading_is_the_bit_block h, lane_reading_is_the_bit_block h]

/-- ⚑⚑⚑ **THE RE-LIMBING IS INJECTIVE.** Two rows this descriptor accepts whose published BYTE
blocks agree have the same 254 bits and therefore the same published LANE block — so the chain's
spelling determines the link's, which is exactly what tie 2 must transport.

⚑ The hypothesis that carries it is BOOLEANITY, and it is the descriptor's own
(`the_row_gates_force_boolean_bits`). `the_booleanity_hypothesis_is_load_bearing` exhibits the
alias that appears when it is dropped. -/
theorem the_relimbing_is_injective {row row' pub pub' : Nat → ℤ}
    (h : relimbRowOk row pub) (h' : relimbRowOk row' pub')
    (hbytes : ∀ i, i < NBYTE → pub (PI_BYTE i) = pub' (PI_BYTE i)) :
    (∀ j, j < NBIT → row (BIT j) = row' (BIT j))
      ∧ (∀ l, l < NLANE → pub (PI_LANE l) = pub' (PI_LANE l)) := by
  have hb := the_row_gates_force_boolean_bits h
  have hb' := the_row_gates_force_boolean_bits h'
  -- every byte's run agrees, so every bit inside it agrees
  have hbit : ∀ j, j < NBIT → row (BIT j) = row' (BIT j) := by
    intro j hj
    obtain ⟨ht, hi⟩ := bit_in_its_byte hj
    have hidx : SB * (j / SB) + j % SB = j := by unfold SB at *; omega
    have hrun : bitSumAt row (SB * (j / SB)) (byteWidth (j / SB))
        = bitSumAt row' (SB * (j / SB)) (byteWidth (j / SB)) := by
      rw [← h.2.1 _ hi, ← h'.2.1 _ hi, ← h.2.2.2.1 _ hi, ← h'.2.2.2.1 _ hi]
      exact hbytes _ hi
    have hres := bitSumAt_inj (f := row) (g := row') (base := SB * (j / SB)) (byteWidth (j / SB))
      (fun t ht' => hb _ (byte_run_inside hi ht'))
      (fun t ht' => hb' _ (byte_run_inside hi ht'))
      hrun (j % SB) ht
    rw [show BIT (SB * (j / SB) + j % SB) = BIT j by rw [hidx]] at hres
    exact hres
  refine ⟨hbit, fun l hl => ?_⟩
  rw [h.2.2.2.2 l hl, h'.2.2.2.2 l hl, h.2.2.1 l hl, h'.2.2.1 l hl]
  exact bitSumAt_congr (fun t ht => hbit _ (lane_run_inside hl ht))

/-! ### §6a — ⚑⚑⚑ THE ALIAS, EXHIBITED.

The shape `Bridge.MinaPackInjective.the_range_hypothesis_is_load_bearing` has, one rail down. There
the alias was `packToFields ⟨[], [(1,1),(0,1)]⟩ = [2] = packToFields ⟨[], [(0,1),(2,1)]⟩` — *"two
different bodies, the same 49 absorbed elements, the same `state_body_hash`, the same root, every
link honest."*

Here it is: **two different `BODYHASH` nonets, the same thirty-two chain limbs, the same
`state_body_hash`, the same root, every link honest.** An injectivity theorem with no exhibited
alias is a claim; with one it is a repair. -/

/-- Bit column 28 carrying `2` — over-wide by one bit, and exactly what booleanity refuses. -/
def aliasBitsA : Nat → ℤ := fun j => if j = 28 then 2 else 0

/-- Bit column 29 carrying `1` — in range, boolean, and a DIFFERENT vector. -/
def aliasBitsB : Nat → ℤ := fun j => if j = 29 then 1 else 0

/-- ⚑ **WHY 28 AND 29 ARE THE PAIR.** Both live in byte 3 (`24 ≤ j < 32`) and they straddle the
lane 0 / lane 1 boundary (`laneStart 1 = 29`). Checked, not asserted — a pair chosen inside one
lane would move nothing and the control would be a no-op, which is how a sibling lane's first
falsifier died. -/
theorem the_alias_pair_straddles_a_lane_boundary_inside_one_byte :
    28 / SB = 3 ∧ 29 / SB = 3 ∧ laneStart 1 = 29
      ∧ 28 < laneStart 1 ∧ laneStart 1 ≤ 29 ∧ 29 < laneStart 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑⚑⚑ **THE BOOLEANITY HYPOTHESIS IS LOAD-BEARING — THE ALIAS, EXHIBITED.** All thirty-two byte
readings agree; two of the nine lane readings do not. So a re-limbing whose bits were not gated
would carry the chain's spelling faithfully and the link's spelling to a different felt, with every
other object in the tower honest. -/
theorem the_booleanity_hypothesis_is_load_bearing :
    ((List.range NBYTE).map (fun i => bitSumAt aliasBitsA (SB * i) (byteWidth i)))
        = ((List.range NBYTE).map (fun i => bitSumAt aliasBitsB (SB * i) (byteWidth i)))
      ∧ ((List.range NLANE).map (fun l => bitSumAt aliasBitsA (laneStart l) (laneWidth l)))
        = [2 ^ 29, 0, 0, 0, 0, 0, 0, 0, 0]
      ∧ ((List.range NLANE).map (fun l => bitSumAt aliasBitsB (laneStart l) (laneWidth l)))
        = [0, 1, 0, 0, 0, 0, 0, 0, 0]
      ∧ aliasBitsA 28 * (aliasBitsA 28 - 1) ≠ 0
      ∧ (∀ j < NBIT, aliasBitsB (BIT j) = 0 ∨ aliasBitsB (BIT j) = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro j _
    unfold aliasBitsB BIT
    split <;> simp

/-- ⚑ **AND THE ALIAS'S TWO BYTE BLOCKS ARE NOT THE ZERO VECTOR** — byte 3 carries `32` on BOTH
sides, so the agreement above is an equality between two things that could have differed rather
than two copies of a constant. ⚠ This is the control a falsifier needs to not be vacuous. -/
theorem the_alias_byte_block_is_non_zero :
    bitSumAt aliasBitsA (SB * 3) (byteWidth 3) = 32
      ∧ bitSumAt aliasBitsB (SB * 3) (byteWidth 3) = 32
      ∧ bitSumAt aliasBitsA (laneStart 0) (laneWidth 0)
          ≠ bitSumAt aliasBitsB (laneStart 0) (laneWidth 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## §7 — ⚑ SATISFIABILITY, PROVED GENERALLY RATHER THAN AT ONE BLOCK.

⚠ The sibling descriptors' honest poles are a `native_decide` at ONE real witness. Here the general
fact is available and is strictly stronger, so it is what gets proved: **every canonical value has
an accepted row.** `MinaBodyHashRelimbSeams` instantiates it at the devnet block's own
`state_body_hash`, so the real-block instance is a corollary rather than the statement. -/

/-- Bit `j` of a natural. -/
def bitOf (v j : Nat) : Nat := v / 2 ^ j % 2

/-- The honest row for value `v`: its bits, then the two spellings its gates compute. -/
def rowOfValue (v : Nat) : Nat → ℤ := fun c =>
  if c < NBIT then (bitOf v c : ℤ)
  else if c < NBIT + NBYTE then bitSumAt (fun d => (bitOf v d : ℤ)) (SB * (c - NBIT)) (byteWidth (c - NBIT))
  else if c < RELIMB_WIDTH then
    bitSumAt (fun d => (bitOf v d : ℤ)) (laneStart (c - NBIT - NBYTE)) (laneWidth (c - NBIT - NBYTE))
  else 0

/-- The honest claim for value `v`: the byte block, then the lane block. -/
def pubOfValue (v : Nat) : Nat → ℤ := fun s =>
  if s < NBYTE then rowOfValue v (BYTE s)
  else if s < RELIMB_PI_COUNT then rowOfValue v (LANE (s - NBYTE))
  else 0

private theorem mod_mul_split (s a b : Nat) : s % (a * b) = a * (s / a % b) + s % a := by
  conv_lhs => rw [← Nat.div_add_mod (s % (a * b)) a]
  rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ ⟨b, rfl⟩]

/-- ⚑ **A RUN OF A VALUE'S OWN BITS IS THAT SLICE OF THE VALUE.** The bridge between the bit block
and base-`2^k` arithmetic, general in the base and the length. -/
theorem bitSumAt_bitOf (v : Nat) : ∀ (base n : Nat),
    bitSumAt (fun d => (bitOf v d : ℤ)) base n = ((v / 2 ^ base % 2 ^ n : ℕ) : ℤ) := by
  intro base n
  induction n with
  | zero => simp [bitSumAt_zero]
  | succ k ih =>
      rw [bitSumAt_succ, ih]
      have hsplit : v / 2 ^ base % 2 ^ (k + 1)
          = 2 ^ k * (v / 2 ^ base / 2 ^ k % 2) + v / 2 ^ base % 2 ^ k := by
        rw [pow_succ]
        exact mod_mul_split (v / 2 ^ base) (2 ^ k) 2
      have hdiv : v / 2 ^ base / 2 ^ k = v / 2 ^ (base + k) := by
        rw [Nat.div_div_eq_div_mul, ← pow_add]
      rw [hsplit, hdiv]
      show _ = ((2 ^ k * bitOf v (base + k) + v / 2 ^ base % 2 ^ k : ℕ) : ℤ)
      unfold bitOf BIT
      push_cast
      ring

/-- ⚑⚑ **EVERY CANONICAL VALUE HAS AN ACCEPTED ROW.** `v < 2^254` — the link's own canonicality
reading — and the row its bits induce satisfies every one of the five leg families. ⚠ Proved
generally: this is not "the real block proves", it is "there is no canonical value that does not".
Kernel-clean, no `native_decide`. -/
theorem every_canonical_value_has_an_accepted_row (v : Nat) :
    relimbRowOk (rowOfValue v) (pubOfValue v) := by
  have hbit : ∀ c, c < NBIT → rowOfValue v (BIT c) = (bitOf v c : ℤ) := by
    intro c hc; unfold rowOfValue BIT; simp [hc]
  have hbitfun : ∀ (base n : Nat), (∀ t, t < n → base + t < NBIT) →
      bitSumAt (rowOfValue v) base n = bitSumAt (fun d => (bitOf v d : ℤ)) base n := by
    intro base n hin
    exact bitSumAt_congr (fun t ht => by rw [hbit _ (hin t ht)]; rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hbit j hj]
    have : bitOf v j = 0 ∨ bitOf v j = 1 := by
      unfold bitOf; omega
    rcases this with h0 | h0 <;> rw [h0] <;> norm_num
  · intro i hi
    have hcol : rowOfValue v (BYTE i)
        = bitSumAt (fun d => (bitOf v d : ℤ)) (SB * i) (byteWidth i) := by
      have h1 : ¬ (BYTE i < NBIT) := by unfold BYTE; omega
      have h2 : BYTE i < NBIT + NBYTE := by unfold BYTE NBYTE SK at *; omega
      have hidx : BYTE i - NBIT = i := by unfold BYTE; omega
      simp only [rowOfValue]
      rw [if_neg h1, if_pos h2, hidx]
    rw [hcol, hbitfun]
    intro t ht
    exact byte_run_inside hi ht
  · intro l hl
    have hcol : rowOfValue v (LANE l)
        = bitSumAt (fun d => (bitOf v d : ℤ)) (laneStart l) (laneWidth l) := by
      have h1 : ¬ (LANE l < NBIT) := by unfold LANE NBYTE SK; omega
      have h2 : ¬ (LANE l < NBIT + NBYTE) := by unfold LANE; omega
      have h3 : LANE l < RELIMB_WIDTH := by
        unfold LANE RELIMB_WIDTH NBYTE SK NLANE at *; omega
      have hidx : LANE l - NBIT - NBYTE = l := by unfold LANE; omega
      simp only [rowOfValue]
      rw [if_neg h1, if_neg h2, if_pos h3, hidx]
    rw [hcol, hbitfun]
    intro t ht
    exact lane_run_inside hl ht
  · intro i hi
    have h1 : PI_BYTE i < NBYTE := by unfold PI_BYTE; omega
    simp only [pubOfValue]
    rw [if_pos h1]
    rfl
  · intro l hl
    have h1 : ¬ (PI_LANE l < NBYTE) := by unfold PI_LANE; omega
    have h2 : PI_LANE l < RELIMB_PI_COUNT := by
      unfold PI_LANE RELIMB_PI_COUNT at *; omega
    have hidx : PI_LANE l - NBYTE = l := by unfold PI_LANE; omega
    simp only [pubOfValue]
    rw [if_neg h1, if_pos h2, hidx]

/-- ⚑ **AND THE ACCEPTED ROW'S TWO SPELLINGS ARE THE VALUE ITSELF** — the byte block reads back as
`v mod 2^254` and so does the lane block. At `v < 2^254` that is `v`, which is what makes the seam
transport a VALUE rather than a residue. -/
theorem the_accepted_row_denotes_its_value (v : Nat) :
    claimByteValue (pubOfValue v) = ((v % 2 ^ NBIT : ℕ) : ℤ)
      ∧ claimLaneValue (pubOfValue v) = ((v % 2 ^ NBIT : ℕ) : ℤ) := by
  have h := every_canonical_value_has_an_accepted_row v
  have hb : claimByteValue (pubOfValue v) = bitSumAt (rowOfValue v) 0 NBIT :=
    byte_reading_is_the_bit_block h
  have hl : claimLaneValue (pubOfValue v) = bitSumAt (rowOfValue v) 0 NBIT :=
    lane_reading_is_the_bit_block h
  have hval : bitSumAt (rowOfValue v) 0 NBIT = ((v % 2 ^ NBIT : ℕ) : ℤ) := by
    have hcong : bitSumAt (rowOfValue v) 0 NBIT
        = bitSumAt (fun d => (bitOf v d : ℤ)) 0 NBIT := by
      refine bitSumAt_congr (fun t ht => ?_)
      unfold rowOfValue BIT
      simp [ht]
    rw [hcong, bitSumAt_bitOf]
    simp
  exact ⟨by rw [hb, hval], by rw [hl, hval]⟩

/-! ## §8 — ⚑ BOTH POLARITIES, at the descriptor's own row predicate.

⚠ Every forgery below MOVES a value the honest row carries, checked rather than assumed — the
control class a `replacen` that no longer matched once killed silently. -/

/-- A concrete canonical witness: `2^253 + 12345`, below `2^254` and non-zero in both spellings. -/
def demoValue : Nat := 2 ^ 253 + 12345

def demoRow : Nat → ℤ := rowOfValue demoValue
def demoPub : Nat → ℤ := pubOfValue demoValue

theorem the_demo_row_is_accepted : relimbRowOk demoRow demoPub :=
  every_canonical_value_has_an_accepted_row demoValue

/-- ⚑ The falsifier's targets carry NON-ZERO honest values — so no mutation below is a no-op. -/
theorem the_falsifier_targets_are_non_zero :
    demoRow (BIT 0) = 1 ∧ demoRow (BYTE 0) ≠ 0 ∧ demoRow (LANE 8) ≠ 0
      ∧ demoPub (PI_BYTE 0) ≠ 0 ∧ demoPub (PI_LANE 8) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- A bit column carrying `2` — the alias's own left half, as a forged row. -/
def forgedBitRow : Nat → ℤ := fun c => if c = BIT 28 then 2 else demoRow c

/-- A published byte that is not what its bits compose. -/
def forgedByteRow : Nat → ℤ := fun c => if c = BYTE 0 then demoRow c + 1 else demoRow c

/-- A published lane that is not what ITS bits compose — the half a byte-only gate would miss. -/
def forgedLaneRow : Nat → ℤ := fun c => if c = LANE 0 then demoRow c + 1 else demoRow c

/-- A claim whose lane slot is not the column it pins. -/
def forgedLanePub : Nat → ℤ := fun s => if s = PI_LANE 8 then demoPub s + 1 else demoPub s

theorem an_over_wide_bit_is_refused : ¬ relimbRowOk forgedBitRow demoPub := by
  intro h
  have hbad : ¬ (forgedBitRow (BIT 28) * (forgedBitRow (BIT 28) - 1) = 0) := by native_decide
  exact hbad (h.1 28 (by decide))

theorem a_byte_that_is_not_its_bits_is_refused : ¬ relimbRowOk forgedByteRow demoPub := by
  intro h
  have hbad : forgedByteRow (BYTE 0) ≠ bitSumAt forgedByteRow (SB * 0) (byteWidth 0) := by
    native_decide
  exact hbad (h.2.1 0 (by decide))

theorem a_lane_that_is_not_its_bits_is_refused : ¬ relimbRowOk forgedLaneRow demoPub := by
  intro h
  have hbad : forgedLaneRow (LANE 0) ≠ bitSumAt forgedLaneRow (laneStart 0) (laneWidth 0) := by
    native_decide
  exact hbad (h.2.2.1 0 (by decide))

theorem a_claim_that_is_not_its_column_is_refused : ¬ relimbRowOk demoRow forgedLanePub := by
  intro h
  have hbad : forgedLanePub (PI_LANE 8) ≠ demoRow (LANE 8) := by native_decide
  exact hbad (h.2.2.2.2 8 (by decide))

/-- ⚑ **BOTH POLARITIES, AS ONE STATEMENT.** -/
theorem relimb_discriminates :
    relimbRowOk demoRow demoPub
      ∧ ¬ relimbRowOk forgedBitRow demoPub
      ∧ ¬ relimbRowOk forgedByteRow demoPub
      ∧ ¬ relimbRowOk forgedLaneRow demoPub
      ∧ ¬ relimbRowOk demoRow forgedLanePub :=
  ⟨the_demo_row_is_accepted, an_over_wide_bit_is_refused,
   a_byte_that_is_not_its_bits_is_refused, a_lane_that_is_not_its_bits_is_refused,
   a_claim_that_is_not_its_column_is_refused⟩

/-! ## §9 — ⚠ RESIDUALS, NAMED.

1. ⚠ **THIS DESCRIPTOR TIES NOTHING BY ITSELF.** It publishes two spellings of one value; WHICH
   value is the seams' business (`MinaBodyHashRelimbSeams`), and those are `cb.connect`s a fold
   issues — recursion wiring with a theorem attached, on the undischarged FRI/STARK floor, exactly
   like every other seam in this cone.
2. ⚠ **IT IS 254 BITS AND THE CHAIN IS 256.** A chain limb block denoting a value in `[2^254, pN)`
   has no accepted row here and the byte seam is unsatisfiable against it. That is a REFUSAL, not a
   silent truncation — but it is a refusal, and a body hash in that window (a fraction `≈ 2^-189`
   of `Fp`) would halt rather than weld.
3. ⚠ **NOTHING HERE SAYS THE VALUE IS A `state_body_hash`.** That is the chain's
   (`MinaStateBodyHashChain.the_body_chain_ends_on_the_state_body_hash`) and the seam's, not this
   descriptor's.
-/

#assert_compiled the_two_partitions_cover_the_same_bits
#assert_compiled the_lane_boundaries_fall_inside_bytes
#assert_compiled the_layout_is_wellformed
#assert_axioms bitSumAt_succ
#assert_axioms bitSumAt_split
#assert_axioms bitSumAt_congr
#assert_axioms bitSumAt_bounds
#assert_axioms bitSumAt_inj
#assert_axioms digitsValW_SB
#assert_axioms digitsValW_succ
#assert_axioms digitsValW_congr
#assert_axioms digitsValW_of_runs
#assert_axioms bitBoolLeg_eq
#assert_axioms termValue_runTerms
#assert_compiled the_gate_coefficients_are_in_field
#assert_compiled no_published_column_is_inert
#assert_compiled relimbAir_leg_count
#assert_axioms relimbAir_mainRailOk
#assert_axioms relimbAir_pinsFit
#assert_axioms the_relimbing_has_no_lookup_bill
#assert_axioms relimbDesc_name
#assert_axioms relimbDesc_width
#assert_axioms relimbDesc_piCount
#assert_axioms relimbDesc_tables
#assert_compiled relimbDesc_constraint_count
#assert_compiled the_lookup_constraint_count_is_zero
#assert_compiled relimb_products_are_only_the_bits
#assert_axioms the_row_gates_force_boolean_bits
#assert_axioms the_two_spellings_denote_one_value
#assert_axioms the_relimbing_is_injective
#assert_compiled the_alias_pair_straddles_a_lane_boundary_inside_one_byte
#assert_axioms bitSumAt_bitOf
#assert_axioms every_canonical_value_has_an_accepted_row
#assert_axioms the_accepted_row_denotes_its_value

-- ⚑ COMPILER-TRUSTED, and said out loud: each evaluates a 254-summand bit fold at a concrete row.
#assert_compiled the_booleanity_hypothesis_is_load_bearing
#assert_compiled the_alias_byte_block_is_non_zero
#assert_compiled the_falsifier_targets_are_non_zero
#assert_compiled an_over_wide_bit_is_refused
#assert_compiled a_byte_that_is_not_its_bits_is_refused
#assert_compiled a_lane_that_is_not_its_bits_is_refused
#assert_compiled a_claim_that_is_not_its_column_is_refused

#assert_compiled laneWidth_top
#assert_compiled byteWidth_top
end Dregg2.Circuit.Emit.MinaBodyHashRelimbAir
