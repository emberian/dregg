/-
# Market.MpcClearingSecurity — exact `(p*, V*)` leakage for volume-argmax clearing

This module joins the actual fhEgg clearing semantics to the output-boundary MPC
security statement.  The runtime rule is

    p* = FhEggClearing.crossing bk K
    V* = FhEggClearing.clearedVolume bk K

where `crossing` is the LOWEST bucket maximizing `min demand supply`.  The public
deterministic view contains only `(p*, V*)` plus public circuit shape.  In
particular it contains no balance sign vector and does not use `balanceCrossing`.

The public shape is `(K, b)` — `K` price buckets, `b`-bit values — and EVERY size
in the transcript is derived from it by the accounting transcribed from `mpc.rs`
in §2.  Nothing here takes a transcript size as an input.

PROVEN here:

* additive n-of-n shares are perfectly hiding from every coalition missing one
  party, with full-collusion teeth;
* the real deterministic view factors exactly through the volume-argmax leakage —
  and so does the FULL view carrying the masked opening CONTENTS: for every
  wire-secret vector a pad-space bijection maps the real transcript onto the
  simulator's output on a uniform sample (`fullView_reveal_only`,
  `masked_lane_secret_independent`), with the padless opening REFUTED as the
  other pole — the §1 primitive now constrains the deployed view instead of
  licensing an abstraction in prose;
* DATA-OBLIVIOUSNESS: every transcript size is a function of `(K,b)` alone, so
  swapping the private book moves nothing the world can see — this used to be
  the hypothesis `hm` and is now `transcript_sizes_depend_only_on_shape`;
* the opened `p*` field is exactly wide enough for every bucket;
* same-leakage books have identical views, while a private curve coefficient and
  the obsolete balance sign do not factor through that leakage;
* the same clearing is conserving, uniform-price optimal, volume maximizing, and
  reveal-only;
* MaskedBoundaryParty's mod-t row identity reconstructs the hidden coefficient,
  and any correct A2B bit representation denotes that same reconstruction;
* generic reveal-only stages compose, and the exact view instantiates PerfectZK.

HONEST SCOPE: this is the semi-honest, perfect-hiding algebra.  Authentication,
malicious-share validity, dealer-free triples, smudging-to-full-transcript hybrids,
and adaptive/UC composition remain outside this theorem.  The A2B bridge specifies
semantic reconstruction; it does not pretend to verify the Rust gate schedule.

⚠ And say plainly what `reveal_only` is: it is `rfl`, and it stays `rfl`.  The view
is DEFINED as the simulation, so that equation is true by construction and is not
where the content lives.  What changed in the §2 rework is what it is definitional
ABOUT — the sizes are now the deployed circuit's, forced, instead of a free field
that any number satisfied.  The load-bearing statements are the ones that are NOT
definitional: `transcript_sizes_depend_only_on_shape` (was the hypothesis `hm`),
`pStar_fits_idxBits`, `maskedOpens_three_never_144`, the satisfiable/refutable pair
`maskedOpens_factors_through_leakage` + `book_reading_size_refutes_factorization`,
and the measured Rust pin.  A reader who cites `reveal_only` alone is citing a
definition.

Pure.
-/
import Market.FhEggClearing
import Market.CertF
import Market.RevealNothing
import Metatheory.Open.PerfectZK
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Abel
import Dregg2.Tactics

namespace Market.MpcClearingSecurity

open Market
open Matrix

set_option autoImplicit false

/-! ## 1. Information-theoretic perfect hiding of additive shares. -/

section PerfectHiding

variable {G : Type*} [AddCommGroup G]

/-- A valid additive n-sharing of `secret`. -/
abbrev Sharing (n : ℕ) (secret : G) : Type _ := { s : Fin n → G // ∑ i, s i = secret }

/-- Rebalance one coordinate by `δ`. -/
def rebalanceFn (n : ℕ) (j : Fin n) (δ : G) (s : Fin n → G) : Fin n → G :=
  Function.update s j (s j + δ)

theorem sum_rebalanceFn {n : ℕ} (s : Fin n → G) (j : Fin n) (δ : G) :
    ∑ i, rebalanceFn n j δ s i = (∑ i, s i) + δ := by
  unfold rebalanceFn
  rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
  have hs : ∑ i, s i = s j + ∑ i ∈ Finset.univ \ {j}, s i := by
    conv_lhs => rw [← Function.update_eq_self j s]
    rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
  rw [hs]
  abel

theorem rebalanceFn_of_ne {n : ℕ} (s : Fin n → G) (j : Fin n) (δ : G)
    {i : Fin n} (hi : i ≠ j) : rebalanceFn n j δ s i = s i := by
  unfold rebalanceFn
  exact Function.update_of_ne hi _ _

/-- A view-preserving bijection between sharings of any two secrets. -/
def rebalanceEquiv (n : ℕ) (j : Fin n) (x y : G) : Sharing n x ≃ Sharing n y where
  toFun s := ⟨rebalanceFn n j (y - x) s.val, by rw [sum_rebalanceFn, s.2]; abel⟩
  invFun s := ⟨rebalanceFn n j (x - y) s.val, by rw [sum_rebalanceFn, s.2]; abel⟩
  left_inv s := by
    apply Subtype.ext
    show rebalanceFn n j (x - y) (rebalanceFn n j (y - x) s.val) = s.val
    unfold rebalanceFn
    simp only [Function.update_self, Function.update_idem]
    rw [show s.val j + (y - x) + (x - y) = s.val j from by abel,
      Function.update_eq_self]
  right_inv s := by
    apply Subtype.ext
    show rebalanceFn n j (y - x) (rebalanceFn n j (x - y) s.val) = s.val
    unfold rebalanceFn
    simp only [Function.update_self, Function.update_idem]
    rw [show s.val j + (x - y) + (y - x) = s.val j from by abel,
      Function.update_eq_self]

/-- Any coalition missing `j` has identical views for every pair of secrets. -/
theorem perfect_hiding (n : ℕ) (j : Fin n) (C : Finset (Fin n)) (hj : j ∉ C) (x y : G) :
    ∃ φ : Sharing n x ≃ Sharing n y,
      ∀ (s : Sharing n x), ∀ i ∈ C, (φ s).val i = s.val i :=
  ⟨rebalanceEquiv n j x y,
    fun s i hi => rebalanceFn_of_ne (i := i) s.val j (y - x) (fun h => hj (h ▸ hi))⟩

def canonicalSharing {n : ℕ} [NeZero n] (secret : G) : Sharing n secret :=
  ⟨Function.update 0 ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ secret, by
    rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
    simp⟩

/-- RED: the full party set reconstructs, so perfect hiding cannot survive full collusion. -/
theorem full_collusion_breaks_hiding {n : ℕ} [NeZero n] {x y : G} (hxy : x ≠ y) :
    ¬ ∃ φ : Sharing n x → Sharing n y,
      ∀ (s : Sharing n x) (i : Fin n), (φ s).val i = s.val i := by
  rintro ⟨φ, hpres⟩
  have hval : (φ (canonicalSharing x)).val = (canonicalSharing (n := n) x).val :=
    funext (hpres (canonicalSharing x))
  have hsum : ∑ i, (φ (canonicalSharing x)).val i =
      ∑ i, (canonicalSharing (n := n) x).val i := by rw [hval]
  rw [(φ (canonicalSharing x)).2, (canonicalSharing (n := n) x).2] at hsum
  exact hxy hsum.symm

/-- Beaver's one-time-pad opening is the two-party `ZMod 2` instance. -/
theorem otpMasks (x y : ZMod 2) :
    ∃ φ : Sharing 2 x ≃ Sharing 2 y,
      ∀ (s : Sharing 2 x), ∀ i ∈ ({1} : Finset (Fin 2)), (φ s).val i = s.val i :=
  perfect_hiding 2 0 {1} (by decide) x y

end PerfectHiding

/-! ## 2. Exact volume-argmax leakage and simulation. -/

theorem demand_nonneg {bk : OrderBook} (hb : OrdersValid bk) (p : ℕ) : 0 ≤ demand bk p := by
  unfold demand
  apply List.sum_nonneg
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨o, ho, rfl⟩ := hz
  unfold demandIncr
  split
  · exact hb o ho
  · exact le_refl 0

theorem supply_nonneg {bk : OrderBook} (hb : OrdersValid bk) (p : ℕ) : 0 ≤ supply bk p := by
  unfold supply
  apply List.sum_nonneg
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨o, ho, rfl⟩ := hz
  unfold supplyIncr
  split
  · exact hb o ho
  · exact le_refl 0

theorem execVol_nonneg {bk : OrderBook} (hb : OrdersValid bk) (p : ℕ) :
    0 ≤ execVol bk p := by
  unfold execVol
  exact le_min (demand_nonneg hb p) (supply_nonneg hb p)

theorem clearedVolume_nonneg {bk : OrderBook} (hb : OrdersValid bk) (K : ℕ) :
    0 ≤ clearedVolume bk K :=
  execVol_nonneg hb _

/-- The exact public leakage of the implemented crossing. -/
structure CrossingLeakage where
  pStar : ℕ
  vStar : ℤ
  deriving DecidableEq, Repr

/-! ### The deployed circuit shape and its EXACT transcript accounting.

`mpc.rs` fixes the SIZE of every public transcript field as a function of the
PUBLIC shape `(K, b)` alone — `K` price buckets, `b`-bit values.  That is the
load-bearing fact behind `mpc.rs::simulate` ("the argmax runs the SAME gate count
on every input (data-oblivious), so that count depends only on `(k, b)`"), and it
is transcribed here so the simulator DERIVES the transcript's size instead of
being handed it.

⚠ What this replaced: `MpcView`/`MpcClearing` used to carry `maskedLen : ℕ` as a
FREE FIELD and `mpcSim` took it as an INPUT.  So "the view is simulable from the
leakage plus public shape" fed the simulator the one number whose independence
from the private book was the thing to prove, and `same_leakage_indistinguishable`
took that independence as the hypothesis `hm`.  Nothing in the model could see
that the only two witnesses in the tree both hand-picked `maskedLen := 144`, a
length the deployed circuit cannot emit at `K = 3` for ANY bit width
(`maskedOpens_three_never_144` below).

Each definition names the Rust it mirrors.  The concrete numbers are pinned
against a REAL `mpc_crossing` run in `fhegg-fhe/tests/mpc_lean_transcript_pin.rs`
— two independent sources (this arithmetic model vs. the circuit's measured
behaviour), so a disagreement is a red gate rather than decoration. -/

/-- `mpc.rs::ceil_log2` transcribed: `while x < n { x <<= 1; d += 1 }`.  `n` is
structural fuel — `x` doubles from `1`, so `n` iterations always suffice. -/
def ceilLog2Go (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, d => d
  | fuel + 1, x, d => if x < n then ceilLog2Go n fuel (2 * x) (d + 1) else d

/-- Least `d` with `n ≤ 2 ^ d` (`mpc.rs::ceil_log2`). -/
def ceilLog2 (n : ℕ) : ℕ := ceilLog2Go n n 1 0

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega

private theorem ceilLog2Go_covers (n : ℕ) :
    ∀ (fuel x d : ℕ), x = 2 ^ d → n ≤ 2 ^ (d + fuel) →
      n ≤ 2 ^ ceilLog2Go n fuel x d := by
  intro fuel
  induction fuel with
  | zero => intro x d _ h; simpa [ceilLog2Go] using h
  | succ f ih =>
    intro x d hx h
    show n ≤ 2 ^ (if x < n then ceilLog2Go n f (2 * x) (d + 1) else d)
    by_cases hlt : x < n
    · simp only [hlt, if_true]
      refine ih (2 * x) (d + 1) (by rw [hx]; ring) ?_
      rw [show d + 1 + f = d + (f + 1) from by ring]
      exact h
    · simp only [hlt, if_false]
      subst hx
      omega

/-- `ceilLog2` genuinely covers: the width it reports really does hold `n`. -/
theorem ceilLog2_covers (n : ℕ) : n ≤ 2 ^ ceilLog2 n :=
  ceilLog2Go_covers n n 1 0 (by norm_num) (by simpa using nat_le_two_pow n)

/-- `mpc.rs::index_bits` — the width `p*` is opened at (at least one bit). -/
def idxBits (K : ℕ) : ℕ := max (ceilLog2 K) 1

/-- `mpc.rs::geq_rounds` — a one-bit comparison needs two rounds. -/
def geqRounds (b : ℕ) : ℕ := if b < 2 then 2 else b

/-- `mpc.rs::mpc_crossing`'s AND-gate count: `K` `secure_min`s at `4b` each, plus
the `K-1` argmax-tournament nodes (`geq` at `3b`, a `b`-bit value MUX, and an
`idxBits K`-bit index MUX).  Depends on `(K,b)` only — never on the book. -/
def andGates (K b : ℕ) : ℕ := K * (4 * b) + (K - 1) * (4 * b + idxBits K)

/-- Every Beaver AND gate opens exactly two one-time-padded bits
(`mpc.rs::and_gate` pushes `d` and `e`; `Transcript::is_reveal_only` enforces
`masked.len() == 2 * and_gates`). -/
def maskedOpens (K b : ℕ) : ℕ := 2 * andGates K b

/-- `mpc.rs::crossing_rounds` — modeled online depth. -/
def crossingRounds (K b : ℕ) : ℕ := (geqRounds b + 1) * (1 + ceilLog2 K)

/-- The width premise the deployed circuit actually needs: every aggregate this
clearing is computed from fits the `b`-bit shares it is computed on.

⚠ This is an obligation that only became STATEABLE once `b` existed.  `pStar` and
`vStar` below are the EXACT `crossing`/`clearedVolume` over `ℤ`; the deployed
circuit computes them on `b`-bit shares and wraps.  Without this field an
`MpcClearing` could carry `b = 1` over a book with `demand = 10` and still claim
its `(p*,V*)` was the deployed output — so introducing `b` unaccompanied would
just have traded one free field for another.  `FhEggRustDenotation.MpcInputsFit`
is the same bound stated over the `u32Residue`s that file works in; this one is
over the raw aggregates, and implies it. -/
def CurvesFit (bk : OrderBook) (K b : ℕ) : Prop :=
  ∀ p < K, demand bk p < (2 : ℤ) ^ b ∧ supply bk p < (2 : ℤ) ^ b

/-- The deterministic public view of one deployed crossing: every field of
`mpc.rs::Transcript`, with the one-time-padded opening CONTENTS abstracted to
their COUNT.  That abstraction is DISCHARGED, not assumed: §2b's
`fullView_reveal_only` proves the view WITH the contents is simulable from the
same leakage, via §1's pad algebra. -/
structure MpcView where
  pStar : ℕ
  vStar : ℤ
  buckets : ℕ
  valueBits : ℕ
  pStarBits : ℕ
  vStarBits : ℕ
  andGates : ℕ
  maskedLen : ℕ
  rounds : ℕ
  deriving DecidableEq, Repr

/-- Witness-free simulation from ONLY `(p*,V*)` and the public shape `(K,b)`.
Note what is NOT a parameter: any transcript size. -/
def mpcSim (K b : ℕ) (q : CrossingLeakage) : MpcView :=
  { pStar := q.pStar, vStar := q.vStar
    buckets := K, valueBits := b
    pStarBits := idxBits K, vStarBits := b
    andGates := andGates K b
    maskedLen := maskedOpens K b
    rounds := crossingRounds K b }

/-- One output-boundary clearing on the actual volume-argmax rule, at the public
circuit shape `(K, b)`. -/
structure MpcClearing where
  bk : OrderBook
  hvalid : OrdersValid bk
  K : ℕ
  hK : 0 < K
  b : ℕ
  hb : 0 < b
  hfit : CurvesFit bk K b
  ρ : ℚ
  hρ : 0 < ρ

namespace MpcClearing

variable (mc : MpcClearing)

def pStar : ℕ := crossing mc.bk mc.K
def vStar : ℤ := clearedVolume mc.bk mc.K
def leakage : CrossingLeakage := ⟨mc.pStar, mc.vStar⟩
def mpcView : MpcView :=
  { pStar := mc.pStar, vStar := mc.vStar
    buckets := mc.K, valueBits := mc.b
    pStarBits := idxBits mc.K, vStarBits := mc.b
    andGates := andGates mc.K mc.b
    maskedLen := maskedOpens mc.K mc.b
    rounds := crossingRounds mc.K mc.b }

/-- The actual deterministic transcript factors exactly through `(p*,V*)` and the
public shape — with every size now DERIVED rather than supplied. -/
theorem reveal_only : mc.mpcView = mpcSim mc.K mc.b mc.leakage := rfl

theorem same_leakage_indistinguishable (mc₁ mc₂ : MpcClearing)
    (hK : mc₁.K = mc₂.K) (hb : mc₁.b = mc₂.b)
    (hq : mc₁.leakage = mc₂.leakage) : mc₁.mpcView = mc₂.mpcView := by
  rw [mc₁.reveal_only, mc₂.reveal_only, hK, hb, hq]

/-- **Data-obliviousness — now a theorem, previously the hypothesis `hm`.** Every
SIZE in the public transcript is fixed by the public shape `(K,b)`; the private
book does not appear in any of them. -/
theorem transcript_sizes_depend_only_on_shape (mc₁ mc₂ : MpcClearing)
    (hK : mc₁.K = mc₂.K) (hb : mc₁.b = mc₂.b) :
    mc₁.mpcView.andGates = mc₂.mpcView.andGates ∧
    mc₁.mpcView.maskedLen = mc₂.mpcView.maskedLen ∧
    mc₁.mpcView.rounds = mc₂.mpcView.rounds ∧
    mc₁.mpcView.pStarBits = mc₂.mpcView.pStarBits ∧
    mc₁.mpcView.vStarBits = mc₂.mpcView.vStarBits := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [MpcClearing.mpcView, hK, hb]

/-- The same fact as a swap: replacing the private book outright moves NO size in
the public transcript.  This is `rfl` now, and that is the point — book
independence became definitional instead of hypothesised. -/
theorem transcript_sizes_invariant_under_book_swap
    (bk' : OrderBook) (h' : OrdersValid bk') (hfit' : CurvesFit bk' mc.K mc.b) :
    ({mc with bk := bk', hvalid := h', hfit := hfit'} : MpcClearing).mpcView.maskedLen
      = mc.mpcView.maskedLen := rfl

theorem pStar_lt : mc.pStar < mc.K := crossing_lt mc.bk mc.hK

/-- The opened index field is exactly wide enough: `p* < K ≤ 2 ^ idxBits K`, so
the `idxBits`-bit reveal neither truncates a bucket nor carries spare width. -/
theorem pStar_fits_idxBits : mc.pStar < 2 ^ idxBits mc.K :=
  lt_of_lt_of_le mc.pStar_lt
    (le_trans (ceilLog2_covers mc.K)
      (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)))

theorem vStar_nonneg : 0 ≤ mc.vStar := clearedVolume_nonneg mc.hvalid mc.K

theorem vStar_optimal {q : ℕ} (hq : q < mc.K) : execVol mc.bk q ≤ mc.vStar :=
  clearedVolume_optimal mc.bk mc.K hq

end MpcClearing

/-! ### The retired hand-picked length, refuted; and the deployed-shape pins. -/

/-- At `K = 3` the deployed circuit emits exactly `40b + 8` masked openings. -/
theorem maskedOpens_three (b : ℕ) : maskedOpens 3 b = 40 * b + 8 := by
  have hidx : idxBits 3 = 2 := by decide
  simp only [maskedOpens, andGates, hidx]
  ring

/-- RED: `144` — the length both retired Dark-Bazaar Tier-1 witnesses hand-picked
— is one the deployed circuit CANNOT emit at `K = 3` at any bit width.  The old
free-field model had no way to notice; this theorem makes putting it back a build
failure. -/
theorem maskedOpens_three_never_144 (b : ℕ) : maskedOpens 3 b ≠ 144 := by
  rw [maskedOpens_three]; omega

/-- Deployed-shape pins, measured independently off a real `mpc_crossing` run by
`fhegg-fhe/tests/mpc_lean_transcript_pin.rs`. -/
theorem deployed_transcript_pins :
    (idxBits 3, andGates 3 8, maskedOpens 3 8, crossingRounds 3 8) = (2, 164, 328, 27) ∧
    (idxBits 4, andGates 4 16, maskedOpens 4 16, crossingRounds 4 16) = (2, 454, 908, 51) ∧
    (idxBits 8, andGates 8 32, maskedOpens 8 32, crossingRounds 8 32) = (3, 1941, 3882, 132) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### 2b. The masked opening CONTENTS — §1's pad algebra discharged ON the view.

`MpcView` records only the COUNT of one-time-padded openings, and until now the licence
for abstracting their CONTENTS lived in prose ("§1 is exactly what licenses that
abstraction").  This section replaces the prose with theorems.  The FULL view — every
`MpcView` field PLUS the opened masked bits themselves — is simulable from the leakage
and the public shape: the deployed opening is `secret ⊕ pad` per bit (`mpc.rs::and_gate`
pushes `d = x ^ a`, `e = y ^ b`; XOR is `ZMod 2` addition, each Beaver pad fresh), and
shifting the pad space by the secrets is a BIJECTION that carries the real full view
onto the simulator's output on a uniform sample (`fullView_reveal_only`).  Pairwise,
any two wire-secret vectors induce the same masked lane up to a pad bijection
(`masked_lane_secret_independent`) — the vector form of §1's `rebalanceFn`/`otpMasks`
algebra.  The pair is genuine, not shape-satisfied: an opening that SKIPS its pad
supports no such bijection (`padless_lane_not_secret_independent`).

Honest scope: this binds the §1 primitive to the MODEL's masked lane — the same
transcription of `mpc.rs` the sizes use, pinned by the measured transcript test.  The
model ↔ `mpc.rs` source correspondence itself remains that transcription, exactly as
for the sizes above. -/

/-- The masked lane of one deployed crossing: one `ZMod 2` bit per opening — exactly
`maskedOpens K b` of them, so the type itself carries the count `MpcView.maskedLen`
reports. -/
abbrev MaskedLane (K b : ℕ) := Fin (maskedOpens K b) → ZMod 2

/-- The FULL deterministic view: every `MpcView` field PLUS the masked opening contents. -/
structure MpcFullView (K b : ℕ) where
  base : MpcView
  masked : MaskedLane K b

/-- What the deployed circuit opens on the masked lane: each wire secret one-time-padded
by its fresh Beaver mask (`d = x ^ a` / `e = y ^ b`). -/
def maskedLane {K b : ℕ} (secrets pads : MaskedLane K b) : MaskedLane K b :=
  fun i => secrets i + pads i

/-- §1's rebalance applied at every opened coordinate: shifting the pad space by a fixed
vector is a bijection — the vector form of the `otpMasks` one-time-pad algebra. -/
def padShift {K b : ℕ} (s : MaskedLane K b) : MaskedLane K b ≃ MaskedLane K b where
  toFun pads := fun i => s i + pads i
  invFun opened := fun i => opened i - s i
  left_inv pads := funext fun i => by show s i + pads i - s i = pads i; ring
  right_inv opened := funext fun i => by show s i + (opened i - s i) = opened i; ring

/-- The witness-free FULL simulator: `mpcSim` for every deterministic field, and the
masked lane taken VERBATIM from a uniform sample — it never sees a secret. -/
def fullSim (K b : ℕ) (q : CrossingLeakage) (sample : MaskedLane K b) : MpcFullView K b :=
  { base := mpcSim K b q, masked := sample }

/-- The real full view of one clearing at its wire secrets and Beaver pads. -/
def MpcClearing.fullView (mc : MpcClearing) (secrets pads : MaskedLane mc.K mc.b) :
    MpcFullView mc.K mc.b :=
  { base := mc.mpcView, masked := maskedLane secrets pads }

/-- **The full deployed view — masked CONTENTS included — is perfectly simulable from
`(p*,V*)` plus the public shape.**  For EVERY wire-secret vector there is a bijection
`φ` of the pad space with `fullView secrets = fullSim ∘ φ` pointwise: fed uniform pads,
the real transcript INCLUDING the opened masked bits is exactly the simulator's output
on a uniform sample.  This is the theorem the count-only `MpcView` abstraction was
resting on as prose.  Say plainly where the content is: the equation itself is
definitional once `φ` is exhibited — the content is that ONE `φ`, independent of the
book, works for every pad (perfect simulation as measure-preserving bijection), and
that the padless opening below admits none. -/
theorem fullView_reveal_only (mc : MpcClearing) (secrets : MaskedLane mc.K mc.b) :
    ∃ φ : MaskedLane mc.K mc.b ≃ MaskedLane mc.K mc.b,
      ∀ pads, mc.fullView secrets pads = fullSim mc.K mc.b mc.leakage (φ pads) :=
  ⟨padShift secrets, fun _ => rfl⟩

/-- Pairwise secret-independence of the masked lane: any two wire-secret vectors — any
two private BOOKS, whatever function of the book the wires compute — produce the SAME
masked openings up to a bijection of the fresh pads.  §1's `perfect_hiding`, lifted to
the whole opened transcript. -/
theorem masked_lane_secret_independent {K b : ℕ} (s₁ s₂ : MaskedLane K b) :
    ∃ φ : MaskedLane K b ≃ MaskedLane K b,
      ∀ pads, maskedLane s₁ pads = maskedLane s₂ (φ pads) := by
  refine ⟨padShift (s₁ - s₂), fun pads => funext fun i => ?_⟩
  simp only [maskedLane, padShift, Equiv.coe_fn_mk, Pi.sub_apply]
  ring

/-- An opening that skips its pad — publishes the wire secret verbatim. -/
def padlessLane {K b : ℕ} (secrets _pads : MaskedLane K b) : MaskedLane K b := secrets

/-- RED: the pad is load-bearing.  The padless opening admits NO secret-independent pad
bijection — the all-zero and all-one secret vectors produce openings no `φ` reconciles.
So `masked_lane_secret_independent` is met on the deployed opening's merits, not by the
shape of the statement. -/
theorem padless_lane_not_secret_independent :
    ¬ ∃ φ : MaskedLane 3 8 ≃ MaskedLane 3 8,
      ∀ pads, padlessLane (fun _ => (0 : ZMod 2)) pads
        = padlessLane (fun _ => (1 : ZMod 2)) (φ pads) := by
  rintro ⟨φ, h⟩
  have h0 := congrFun (h 0) ⟨0, by decide⟩
  simp only [padlessLane] at h0
  exact absurd h0 (by decide)

/-! ## 3. RED teeth: the old least-crossing/sign-vector semantics are not this leakage. -/

def bookA : OrderBook := workBook

/-- Same actual output `(1,8)` as `workBook`, but a different private curve and balance sign at 1. -/
def bookB : OrderBook :=
  [ { side := Side.bid, qty := 6, limit := 2 },
    { side := Side.bid, qty := 2, limit := 1 },
    { side := Side.bid, qty := 3, limit := 0 },
    { side := Side.ask, qty := 3, limit := 0 },
    { side := Side.ask, qty := 5, limit := 1 } ]

theorem bookB_valid : OrdersValid bookB := by unfold OrdersValid bookB; decide
theorem bookB_crossing : crossing bookB 3 = 1 := by decide
theorem bookB_clearedVolume : clearedVolume bookB 3 = 8 := by decide
theorem bookAB_demand0_differs : demand bookA 0 = 10 ∧ demand bookB 0 = 11 := by
  constructor <;> decide

/-- RED: the old least balanced bucket is not the implemented clearing price. -/
theorem old_balanceCrossing_disagrees_with_runtime :
    balanceCrossing workBook workBook_crosses ≠ crossing workBook 3 := by
  rw [workBook_balanceCrossing, workBook_crossing]
  decide

/-- RED: the old balance sign is not determined by the actual `(p*,V*)` output. -/
theorem old_sign_not_determined_by_runtime_leakage :
    ¬ ∃ sim : CrossingLeakage → Bool,
      ∀ (bk : OrderBook) (K p : ℕ),
        decide (Clears bk p) = sim ⟨crossing bk K, clearedVolume bk K⟩ := by
  rintro ⟨sim, hsim⟩
  have hA := hsim workBook 3 1
  have hB := hsim bookB 3 1
  rw [workBook_crossing, workBook_clearedVolume] at hA
  rw [bookB_crossing, bookB_clearedVolume] at hB
  have hsignA : decide (Clears workBook 1) = false := by decide
  have hsignB : decide (Clears bookB 1) = true := by decide
  rw [hsignA] at hA
  rw [hsignB] at hB
  exact Bool.false_ne_true (hA.trans hB.symm)

/-- RED: a private curve coefficient cannot be simulated from `(p*,V*)`. -/
theorem mpc_leaky_no_simulator :
    ¬ ∃ sim : CrossingLeakage → ℤ,
      ∀ (bk : OrderBook) (K : ℕ),
        demand bk 0 = sim ⟨crossing bk K, clearedVolume bk K⟩ := by
  rintro ⟨sim, hsim⟩
  have hA := hsim bookA 3
  have hB := hsim bookB 3
  rw [show crossing bookA 3 = 1 from workBook_crossing,
    show clearedVolume bookA 3 = 8 from workBook_clearedVolume] at hA
  rw [bookB_crossing, bookB_clearedVolume] at hB
  rw [(bookAB_demand0_differs).1] at hA
  rw [(bookAB_demand0_differs).2] at hB
  exact absurd (hA.trans hB.symm) (by decide)

/-! ### Is "the transcript size factors through the public leakage" a real constraint?

A property every candidate satisfies constrains nothing.  These two say the
factorization is SATISFIED by the deployed size function and REFUTED by a
book-reading one — so it is a genuine restriction, met on its merits rather than
by the shape of the statement. -/

/-- Satisfiable: the deployed size function factors, because it ignores the book. -/
theorem maskedOpens_factors_through_leakage :
    ∃ s : ℕ → ℕ → CrossingLeakage → ℕ,
      ∀ (bk : OrderBook) (K b : ℕ),
        maskedOpens K b = s K b ⟨crossing bk K, clearedVolume bk K⟩ :=
  ⟨fun K b _ => maskedOpens K b, fun _ _ _ => rfl⟩

/-- RED: refutable — a size function that read one private curve coefficient could
NOT factor, since `bookA`/`bookB` share `(p*,V*) = (1,8)` at `K = 3` yet differ at
`demand · 0`.  Had `maskedLen` stayed a free field, it was free to be exactly such
a function and nothing would have complained. -/
theorem book_reading_size_refutes_factorization :
    ¬ ∃ s : ℕ → ℕ → CrossingLeakage → ℕ,
      ∀ (bk : OrderBook) (K b : ℕ),
        (demand bk 0).toNat = s K b ⟨crossing bk K, clearedVolume bk K⟩ := by
  rintro ⟨s, hs⟩
  have hA := hs bookA 3 8
  have hB := hs bookB 3 8
  rw [show crossing bookA 3 = 1 from workBook_crossing,
    show clearedVolume bookA 3 = 8 from workBook_clearedVolume] at hA
  rw [bookB_crossing, bookB_clearedVolume] at hB
  rw [bookAB_demand0_differs.1] at hA
  rw [bookAB_demand0_differs.2] at hB
  exact absurd (hA.trans hB.symm) (by decide)

/-! ## 4. The joined clearing theorem. -/

theorem cleared_conserving_optimal_and_reveal_only (mc : MpcClearing) :
    ((∀ a, netFlow (clearedBatch (mc.vStar : ℚ) mc.ρ) a = 0) ∧
      (∀ f ∈ clearedBatch (mc.vStar : ℚ) mc.ρ,
        f.filledIn ≤ f.order.offerAmount ∧
        f.order.limitPrice ≤ f.execPrice ∧
        f.filledIn * f.order.limitPrice ≤ f.filledOut) ∧
      (∀ f ∈ clearedBatch (mc.vStar : ℚ) mc.ρ,
        recvValue 0 1 mc.ρ f = spentValue 0 1 mc.ρ f)) ∧
    (∀ q < mc.K, execVol mc.bk q ≤ mc.vStar) ∧
    (mc.mpcView = mpcSim mc.K mc.b mc.leakage ∧
      mc.leakage = ⟨crossing mc.bk mc.K, clearedVolume mc.bk mc.K⟩) := by
  refine ⟨clearedBatch_optimal (mc.vStar : ℚ) mc.ρ ?_ mc.hρ,
    fun q hq => mc.vStar_optimal hq, mc.reveal_only, rfl⟩
  exact_mod_cast mc.vStar_nonneg

def mcA : MpcClearing :=
  { bk := bookA
    hvalid := workBook_valid
    K := 3
    hK := by norm_num
    b := 8
    hb := by norm_num
    hfit := by unfold CurvesFit bookA; decide
    ρ := 2
    hρ := by norm_num }

/-- `mcA`'s transcript sizes are the deployed circuit's, not a chosen number. -/
theorem mcA_transcript_sizes :
    (mcA.mpcView.andGates, mcA.mpcView.maskedLen, mcA.mpcView.rounds,
      mcA.mpcView.pStarBits, mcA.mpcView.vStarBits) = (164, 328, 27, 2, 8) := by
  decide

theorem mcA_leakage : mcA.leakage = ⟨1, 8⟩ := by
  unfold MpcClearing.leakage MpcClearing.pStar MpcClearing.vStar mcA bookA
  rw [workBook_crossing, workBook_clearedVolume]

def mcA_joined := cleared_conserving_optimal_and_reveal_only mcA

/-! ## 5. MaskedBoundaryParty rows and the semantic A2B bridge. -/

section BoundaryRows

variable {n t : ℕ}

/-- Party 0's `y-r₀` and every other party's `-rᵢ`, expressed by rebalancing
the all-negative mask row at the designated public-opening party. -/
def maskedBoundaryRows (j : Fin n) (y : ZMod t) (masks : Fin n → ZMod t) : Fin n → ZMod t :=
  rebalanceFn n j y (fun i => -masks i)

theorem maskedBoundaryRows_designated (j : Fin n) (y : ZMod t) (masks : Fin n → ZMod t) :
    maskedBoundaryRows j y masks j = y - masks j := by
  unfold maskedBoundaryRows rebalanceFn
  simp
  abel

theorem maskedBoundaryRows_other (j : Fin n) (y : ZMod t) (masks : Fin n → ZMod t)
    {i : Fin n} (hi : i ≠ j) : maskedBoundaryRows j y masks i = -masks i :=
  rebalanceFn_of_ne _ j y hi

theorem sum_maskedBoundaryRows (j : Fin n) (y : ZMod t) (masks : Fin n → ZMod t) :
    ∑ i, maskedBoundaryRows j y masks i = y - ∑ i, masks i := by
  unfold maskedBoundaryRows
  rw [sum_rebalanceFn]
  simp only [Finset.sum_neg_distrib]
  abel

/-- If the only opened value is `y=m+Σrᵢ`, the party-local rows reconstruct `m`. -/
theorem maskedBoundary_reconstruct (j : Fin n) (m y : ZMod t) (masks : Fin n → ZMod t)
    (hpad : y = m + ∑ i, masks i) : ∑ i, maskedBoundaryRows j y masks i = m := by
  rw [sum_maskedBoundaryRows, hpad]
  abel

/-- Numeric value represented by a little-endian boolean vector. -/
def bitsValue {w : ℕ} (bits : Fin w → Bool) : ℕ :=
  ∑ i, if bits i then 2 ^ (i : ℕ) else 0

/-- Semantic contract of the distributed A2B result: its bits are in the declared
`w`-bit range and denote the mod-t sum of the source-party arithmetic rows. -/
def A2BRepresents {w : ℕ} (rows : Fin n → ZMod t) (bits : Fin w → Bool) : Prop :=
  bitsValue bits < 2 ^ w ∧ (bitsValue bits : ZMod t) = ∑ i, rows i

/-- Composition of masked-boundary reconstruction with a correct A2B encoding.
The upstream `< 2^w` bound that makes Rust truncation exact is an explicit
hypothesis; this theorem does not invent a malicious range check. -/
theorem maskedBoundary_a2b_semantic {w : ℕ} (j : Fin n) (m y : ZMod t) (mNat : ℕ)
    (masks : Fin n → ZMod t) (bits : Fin w → Bool)
    (hpad : y = m + ∑ i, masks i) (hrep : (mNat : ZMod t) = m)
    (hrange : mNat < 2 ^ w) (hbits : bitsValue bits = mNat) :
    A2BRepresents (maskedBoundaryRows j y masks) bits := by
  unfold A2BRepresents
  constructor
  · rw [hbits]
    exact hrange
  · rw [maskedBoundary_reconstruct j m y masks hpad, hbits]
    exact hrep

end BoundaryRows

/-! ## 6. Cert-F and modular composition. -/

structure CertifiedMpcClearing (V E : Type*) [Fintype V] [Fintype E] where
  lp : FlowLP V E ℤ
  f : E → ℤ
  π : V → ℤ
  s : E → ℤ
  cert : Certified lp f π s
  K : ℕ
  b : ℕ
  leak : CrossingLeakage
  view : MpcView
  reveal : view = mpcSim K b leak

theorem certified_epsilon_optimal_and_reveal_only {V E : Type*} [Fintype V] [Fintype E]
    (cmc : CertifiedMpcClearing V E) {f' : E → ℤ} (hf' : PrimalFeasible cmc.lp f') :
    (cmc.lp.w ⬝ᵥ f' ≤ cmc.lp.w ⬝ᵥ cmc.f + cmc.lp.ε) ∧
    (cmc.view = mpcSim cmc.K cmc.b cmc.leak) :=
  ⟨certifies_epsilon_optimal cmc.lp cmc.cert hf', cmc.reveal⟩

theorem compose_reveals_only {A B QA QB VA VB : Type*}
    (v₁ : A → VA) (s₁ : QA → VA) (q₁ : A → QA) (h₁ : ∀ a, v₁ a = s₁ (q₁ a))
    (v₂ : B → VB) (s₂ : QB → VB) (q₂ : B → QB) (h₂ : ∀ b, v₂ b = s₂ (q₂ b)) :
    ∀ (a : A) (b : B),
      (v₁ a, v₂ b) = (fun p : QA × QB => (s₁ p.1, s₂ p.2)) (q₁ a, q₂ b) := by
  intro a b
  simp only [h₁, h₂]

theorem fold_then_crossing_reveals_only
    {A QA VA : Type*} (foldView : A → VA) (foldSim : QA → VA) (foldLeak : A → QA)
    (hfold : ∀ a, foldView a = foldSim (foldLeak a)) (mc : MpcClearing) :
    ∀ a, (foldView a, mc.mpcView) =
      (fun p : QA × CrossingLeakage =>
        (foldSim p.1, mpcSim mc.K mc.b p.2)) (foldLeak a, mc.leakage) := by
  intro a
  simp only [hfold a, mc.reveal_only]

/-! ## 7. PerfectZK bridge. -/

open Metatheory.Open.PerfectZK

def mpcPerfectZK (K b : ℕ) : PerfectZK where
  S := CrossingLeakage
  W := MpcClearing
  V := MpcView
  view q _ := mpcSim K b q
  sim q := mpcSim K b q
  hperf _ _ := rfl

theorem mpcView_eq_perfectZK (mc : MpcClearing) :
    mc.mpcView = (mpcPerfectZK mc.K mc.b).view mc.leakage mc :=
  mc.reveal_only

theorem mpc_reveal_nothing (K b : ℕ) (q : CrossingLeakage)
    (mc₁ mc₂ : MpcClearing) :
    (mpcPerfectZK K b).view q mc₁ = (mpcPerfectZK K b).view q mc₂ :=
  (mpcPerfectZK K b).view_indep_of_witness q mc₁ mc₂

/-! RED/positive teeth, as named theorems (see `metatheory/docs/GUARD-DISCIPLINE.md`
— these were five `#guard`s, i.e. the same closed instances with the name, the term
and the axiom record deleted). -/

theorem workBook_runtime_clearing : (crossing workBook 3, clearedVolume workBook 3) = (1, 8) := by
  decide

-- The fifth retired `#guard` asserted `balanceCrossing workBook workBook_crosses = 2`,
-- which is already the named, kernel-clean `Market.workBook_balanceCrossing`
-- (`FhEggClearing.lean:465`) — a duplicate, so it is simply dropped.  Note the guard
-- could only ever have passed via the compiled evaluator: `balanceCrossing` is
-- `Nat.find` over an opaque existence proof and does not reduce in the kernel.

theorem bookB_runtime_clearing : (crossing bookB 3, clearedVolume bookB 3) = (1, 8) := by
  decide

theorem workBook_bookB_balance_signs_differ_at_one :
    (decide (Clears workBook 1), decide (Clears bookB 1)) = (false, true) := by
  decide

theorem workBook_bookB_demand0_differs : (demand bookA 0, demand bookB 0) = (10, 11) := by
  decide

/-! Axiom hygiene. -/

#assert_all_clean [Market.MpcClearingSecurity.perfect_hiding,
  Market.MpcClearingSecurity.full_collusion_breaks_hiding,
  Market.MpcClearingSecurity.otpMasks,
  Market.MpcClearingSecurity.ceilLog2_covers,
  Market.MpcClearingSecurity.MpcClearing.reveal_only,
  Market.MpcClearingSecurity.MpcClearing.same_leakage_indistinguishable,
  Market.MpcClearingSecurity.MpcClearing.transcript_sizes_depend_only_on_shape,
  Market.MpcClearingSecurity.MpcClearing.transcript_sizes_invariant_under_book_swap,
  Market.MpcClearingSecurity.MpcClearing.pStar_fits_idxBits,
  Market.MpcClearingSecurity.maskedOpens_three,
  Market.MpcClearingSecurity.maskedOpens_three_never_144,
  Market.MpcClearingSecurity.maskedOpens_factors_through_leakage,
  Market.MpcClearingSecurity.book_reading_size_refutes_factorization,
  Market.MpcClearingSecurity.deployed_transcript_pins,
  Market.MpcClearingSecurity.fullView_reveal_only,
  Market.MpcClearingSecurity.masked_lane_secret_independent,
  Market.MpcClearingSecurity.padless_lane_not_secret_independent,
  Market.MpcClearingSecurity.mcA_transcript_sizes,
  Market.MpcClearingSecurity.workBook_runtime_clearing,
  Market.MpcClearingSecurity.bookB_runtime_clearing,
  Market.MpcClearingSecurity.workBook_bookB_balance_signs_differ_at_one,
  Market.MpcClearingSecurity.workBook_bookB_demand0_differs,
  Market.MpcClearingSecurity.old_balanceCrossing_disagrees_with_runtime,
  Market.MpcClearingSecurity.old_sign_not_determined_by_runtime_leakage,
  Market.MpcClearingSecurity.mpc_leaky_no_simulator,
  Market.MpcClearingSecurity.cleared_conserving_optimal_and_reveal_only,
  Market.MpcClearingSecurity.mcA_joined,
  Market.MpcClearingSecurity.maskedBoundary_reconstruct,
  Market.MpcClearingSecurity.maskedBoundary_a2b_semantic,
  Market.MpcClearingSecurity.certified_epsilon_optimal_and_reveal_only,
  Market.MpcClearingSecurity.compose_reveals_only,
  Market.MpcClearingSecurity.fold_then_crossing_reveals_only,
  Market.MpcClearingSecurity.mpcView_eq_perfectZK,
  Market.MpcClearingSecurity.mpc_reveal_nothing]

end Market.MpcClearingSecurity
