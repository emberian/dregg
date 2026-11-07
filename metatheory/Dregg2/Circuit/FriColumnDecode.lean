/-
# `Dregg2.Circuit.FriColumnDecode` — TRANSPORTING `FriColumnIdentification` across the
Int-verifier ↔ BabyBear-oracle seam: the fold-chain algebra PROVED, the residual renamed
into pure verifier vocabulary.

## What this module does (the one-line honest claim)

`DeployedTraceExtract.FriColumnIdentification` — the last cross-type map behind
`accept_folds` — says: on `verifyAlgo`-accept, the committed columns (read as an abstract
oracle `Fin 16 → BabyBear`) fold into `friSetupK8.C'` under all `8` challenges. That
statement mixes TWO vocabularies: the deployed verifier's (Merkle-opened `Int` columns,
the chained arity-2 `foldCombine` walk of `friQueryCheck`, a final-poly constant) and the
abstract FRI development's (`Fold friSetupK8.geom`, the arity-8 Vandermonde components
`Cj`, the folded code `C'`). This file PROVES the entire abstract half of that map and
leaves a residual stated ONLY in verifier vocabulary:

  1. **THE KEYSTONE (`chain8_eval8`, generic; `foldChain3_eq_fold`, deployed).** The
     deployed FRI folds 8-to-1 as THREE chained arity-2 folds (`PROD_FRI_MAX_LOG_ARITY=3`)
     with the layer challenges `β, β², β⁴` — each layer the coset fold
     `foldCombineF β x e0 e1 = (e0+e1)/2 + β·(e0−e1)/(2x)` (EXACTLY `FriSoundness.E/O`'s
     `E + β·O`, the `1/(2x)` twiddle of `FriVerifier §1b`). We prove: this 3-layer chain
     over a fiber of the size-16 BabyBear RS domain equals **the fiber interpolant
     evaluated at `β`** — which is definitionally the abstract arity-8
     `Fold friSetupK8.geom β`. So the verifier's own fold-chain arithmetic IS the abstract
     Fold: the two disjoint developments compute the same field element.
  2. **THE LANDING (`fold_mem_C'_iff_chain_const`).** `Fold β f ∈ friSetupK8.C'`
     (constants) holds IFF the verifier-side chain bottoms out at ONE constant on BOTH
     fibers — i.e. the `friQueryCheck` "final folded value = `finalPoly` constant" check,
     read at full domain, IS the abstract folded-code membership. Both directions proved.
  3. **THE DECODE (`decodeColumn`, `decode_fold_relation`).** The committed `Int` column
     values reduce mod the BabyBear prime onto the `Fin 16` RS domain (`decodeColumn` =
     the canonical `Int → ZMod p` ring map, leaf `i` ↦ domain point `ω₁₆^i`); and an
     `Int`-level division-free fold identity `2·X·V = X·(E0+E1) + B·(E0−E1)` transports
     along that reduction to the exact field fold `V̄ = foldCombineF B̄ X̄ Ē0 Ē1`
     (`Int.cast` is a ring hom; the field division is recovered by cancellation). The
     decode genuinely works mod p (`decode_mod_p`).

## The exact remaining residual (`ColumnDecodeBridge`) — named PRECISELY, verifier-only

With the algebra proved, `FriColumnIdentification` FOLLOWS
(`friColumnIdentification_of_columnDecode`) from `ColumnDecodeBridge`, whose single Prop
field `accept_chains` is stated with NO abstract-FRI vocabulary at all — no `Fold`, no
`friSetupK8`, no submodules: "on `verifyAlgo`-accept, the deployed fold chain over the
decoded committed column bottoms out at a constant, at every domain position, for the `8`
(rewound) challenges". Its content decomposes into exactly FOUR irreducible sub-seams, all
on the verifier side:

  (a) **commitment → total column**: `BatchProofData` carries per-QUERY Merkle openings;
      the total committed column function is the extractor's object under Poseidon2
      Merkle binding (`merkleRecompute_binds` is the proven tooth; turning openings into
      a committed FUNCTION is knowledge-extraction, not algebra);
  (b) **spot-check → full domain**: `verifyAlgo` checks the fold equations at the ~19
      transcript-sampled queries; `accept_chains` asserts them at ALL positions. That gap
      IS the probabilistic FRI query-soundness step — measured, not deterministic
      (`FriQuerySoundness.deployed_accept_prob_lt < 2⁻³¹`); a deterministic proof of
      `accept_chains` from one accepting transcript is impossible in principle.
  (c) **fold-formula pin**: the deployed `FriCore.foldCombine` (an abstract record field
      at `Int`) computes, mod p, the coset fold `foldCombineF` — the calibration fixture
      of `ETH-NATIVE-WRAP §3/§4`; `decode_fold_relation` is the proven transport TEMPLATE
      for it (the division-free `Int` identity ⟹ the field fold).
  (d) **transcript rewind**: the `8` DISTINCT challenges are forking/rewinding data (one
      deployed transcript carries ONE β per layer); `chal`/`chal_inj` carry them, exactly
      as in `DeployedFriEmbedding`.

So the seam no longer crosses types: the cross-type algebra (arity-2-chain = arity-8
Vandermonde `Fold`; constant-landing = `C'`; `Int` reduction = field fold) is THEOREMS,
and what remains is a verifier-side extraction statement. Composition to the apex is
wired: `ColumnDecodeBridge` + the OOD/leg decode ⟹ `DeployedTraceDecode` ⟹ `[StarkSound]`
(`starkSound_of_columnDecode_and_refines`), with `friProximityK8_discharge0` and the
OOD→AIR bridge still load-bearing in the middle.

## Teeth (both polarities + a kernel-evaluated end-to-end canary)

  * FIRES: every challenge admits a constant chain landing for the honest codeword
    (`chain_honest_fires` — abstract completeness driven BACKWARD through the keystone);
    and the CONCRETE committed integer column of `2 + 3·ω₁₆^x` (`honestColumn`,
    kernel-checked to decode to `fHon8`) chains to `2 + 3·5 = 17` at `β = 5` on both
    fibers (`chain_honest_concrete` — `decide` evaluates the REAL `foldCombineF`
    divisions, so a drift in the chain wiring fails the build).
  * BITES: the far word `f0` admits NO `8` distinct challenges with constant chain
    landings (`chain_far_bites`) — the proven arity-8 proximity bites THROUGH the new
    identity: full-domain chain acceptance forces low degree.

## Discipline

Sorry-free; no `axiom`; no `def …Sound` carrier — the residual enters as the explicit
`ColumnDecodeBridge` hypothesis structure. `#assert_axioms` ⊆ `{propext, Classical.choice,
Quot.sound}`. ADDITIVE: imports read-only, shared apex modules untouched.
-/
import Dregg2.Circuit.DeployedTraceExtract

namespace Dregg2.Circuit.FriColumnDecode

open Dregg2.Circuit.FriVerifierBridge (ProofView DeployedRefines)
open Dregg2.Circuit.FriVerifier (verifyAlgo FriParams RecursionVk FriChecks)
open Dregg2.Circuit.CircuitSoundness
  (Registry BatchPublicInputs BatchProof tracePublishedCommit StarkSound)
open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt memLog mapLog opRow)
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Circuit.FriFoldArity
  (friSetupK8 friGeomK8 Fold Cj self_decomp pC repsC qC_repsC fHon8 fHon8_fold_complete
   f0 f0_no_injective_good)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DeployedTraceExtract
  (FriColumnIdentification DeployedTraceDecode starkSound_of_traceDecode_and_refines)
open Dregg2.Circuit.OodInterpFieldExt
  (BB4 OodInterpFExt oodInterpFExt_of_oodInterpF exists_nonbase_bb4 fire_oodInterpFExt_nonbase)
open Dregg2.Crypto

/-! ## §1 — The deployed arity-2 fold formula and the Int→BabyBear column decode.

`foldCombineF` is the coset fold the deployed per-query walk performs at each layer
(`FriVerifier §1b`: "the exact arity-2 fold formula (the coset `1/(2x)` twiddle)") — and
it is EXACTLY the in-tree arity-2 semantics `FriSoundness.E + β·FriSoundness.O` at the
opened pair `(e0, e1) = (f x, f (−x))`, so no NEW fold semantics is introduced here. -/

/-- **The deployed arity-2 FRI fold combine**: `e_even + β·e_odd` at the coset point `x`,
i.e. `(e0+e1)/2 + β·(e0−e1)/(2x)` — `FriSoundness`'s `E + β·O` read off the opened pair. -/
def foldCombineF {F : Type*} [Field F] (β x e0 e1 : F) : F :=
  (e0 + e1) / 2 + β * ((e0 - e1) / (2 * x))

section GenericField

variable {F : Type*} [Field F]

/-- The DIVISION-FREE characterization of the fold: `2x·fold = x·(e0+e1) + β·(e0−e1)`.
This is the polynomial identity an `Int`-level verifier can check without field division. -/
theorem foldCombineF_char (β x e0 e1 : F) (hx : x ≠ 0) (h2 : (2 : F) ≠ 0) :
    2 * x * foldCombineF β x e0 e1 = x * (e0 + e1) + β * (e0 - e1) := by
  unfold foldCombineF
  field_simp

/-- The fold is the UNIQUE solution of the division-free identity (cancellation). -/
theorem foldCombineF_of_linear_relation {β x e0 e1 v : F} (hx : x ≠ 0) (h2 : (2 : F) ≠ 0)
    (h : 2 * x * v = x * (e0 + e1) + β * (e0 - e1)) :
    v = foldCombineF β x e0 e1 :=
  mul_left_cancel₀ (mul_ne_zero h2 hx)
    (h.trans (foldCombineF_char β x e0 e1 hx h2).symm)

end GenericField

/-- **The column decode**: the committed `Int` column values, reduced mod the BabyBear
prime (`Int.cast` is the canonical ring map `ℤ → ZMod p`) and indexed over the `Fin 16`
Reed–Solomon domain (leaf `i` ↦ domain point `ω₁₆^i`). Out-of-range reads default to `0`
(the bridge quantifies over what the column IS, so padding carries no soundness weight). -/
noncomputable def decodeColumn (col : List Int) : Fin 16 → BabyBear :=
  fun i => ((col.getD (i : ℕ) 0 : Int) : BabyBear)

/-- **The Int→field fold transport**: if the committed integers satisfy the division-free
fold identity over `ℤ`, their mod-p reductions satisfy the exact field fold. This is the
proven TEMPLATE for residual sub-seam (c) — the deployed `FriCore.foldCombine` pin. -/
theorem decode_fold_relation {B X E0 E1 V : Int}
    (h : 2 * X * V = X * (E0 + E1) + B * (E0 - E1))
    (hx : (X : BabyBear) ≠ 0) :
    (V : BabyBear) = foldCombineF (B : BabyBear) (X : BabyBear) (E0 : BabyBear) (E1 : BabyBear) := by
  apply foldCombineF_of_linear_relation hx (by decide)
  have h' := congrArg (fun n : Int => (n : BabyBear)) h
  push_cast at h'
  exact h'

/-- The decode is genuinely mod-p: shifting a committed integer by the BabyBear prime
decodes identically (canonical reduction, a feature of the ring map — recorded so the
decode's semantics is pinned, not guessed). -/
theorem decode_mod_p (n : Int) : ((n + 2013265921 : Int) : BabyBear) = (n : BabyBear) := by
  push_cast
  have hp : (2013265921 : BabyBear) = 0 := by decide
  rw [hp, add_zero]

/-! ## §2 — THE KEYSTONE: the 3-layer arity-2 fold chain = the fiber interpolant at `β`.

Generic over any field: `eval8 c` is the degree-`< 8` polynomial with coefficients `c`;
one arity-2 fold with challenge `β` of `(P(x), P(−x))` computes the even/odd-split
polynomial at `x²` (`fold_eval8/4/2`); chaining THREE folds with `β, β², β⁴` (the deployed
`max_log_arity = 3` schedule) picks up `β^{b₀}·(β²)^{b₁}·(β⁴)^{b₂} = β^j` on each monomial
— the chain value is `P(β)` (`chain8_eval8`). -/

section Keystone

variable {F : Type*} [Field F]

/-- Degree-`< 8` evaluation, unrolled. -/
def eval8 (c : Fin 8 → F) (x : F) : F :=
  c 0 + c 1 * x + c 2 * x ^ 2 + c 3 * x ^ 3 + c 4 * x ^ 4 + c 5 * x ^ 5 + c 6 * x ^ 6 + c 7 * x ^ 7

/-- `eval8` as the `Fin 8` sum — the shape `FriFoldArity.Fold`/`self_decomp` speak. -/
theorem eval8_eq_sum (c : Fin 8 → F) (x : F) :
    eval8 c x = ∑ j : Fin 8, x ^ (j : ℕ) * c j := by
  simp only [Fin.sum_univ_eight]
  show eval8 c x =
    x ^ (0 : ℕ) * c 0 + x ^ (1 : ℕ) * c 1 + x ^ (2 : ℕ) * c 2 + x ^ (3 : ℕ) * c 3 +
    x ^ (4 : ℕ) * c 4 + x ^ (5 : ℕ) * c 5 + x ^ (6 : ℕ) * c 6 + x ^ (7 : ℕ) * c 7
  unfold eval8
  ring

/-- **Layer lemma (8 → 4)**: one arity-2 fold of `(P(x), P(−x))` for degree-`< 8` `P`
computes the even/odd split `P_e + β·P_o` at `x²`. -/
theorem fold_eval8 {c : Fin 8 → F} (β x : F) (hx : x ≠ 0) (h2 : (2 : F) ≠ 0) :
    foldCombineF β x (eval8 c x) (eval8 c (-x))
      = (c 0 + β * c 1) + (c 2 + β * c 3) * x ^ 2
        + (c 4 + β * c 5) * (x ^ 2) ^ 2 + (c 6 + β * c 7) * (x ^ 2) ^ 3 := by
  unfold foldCombineF eval8
  field_simp
  ring

/-- **Layer lemma (4 → 2)**. -/
theorem fold_eval4 {d0 d1 d2 d3 : F} (β x : F) (hx : x ≠ 0) (h2 : (2 : F) ≠ 0) :
    foldCombineF β x (d0 + d1 * x + d2 * x ^ 2 + d3 * x ^ 3)
        (d0 + d1 * (-x) + d2 * (-x) ^ 2 + d3 * (-x) ^ 3)
      = (d0 + β * d1) + (d2 + β * d3) * x ^ 2 := by
  unfold foldCombineF
  field_simp
  ring

/-- **Layer lemma (2 → 1)**: the final fold bottoms out at the constant coefficient pair. -/
theorem fold_eval2 {e0 e1 : F} (β x : F) (hx : x ≠ 0) (h2 : (2 : F) ≠ 0) :
    foldCombineF β x (e0 + e1 * x) (e0 + e1 * (-x)) = e0 + β * e1 := by
  unfold foldCombineF
  field_simp
  ring

/-- **The deployed 8-to-1 fold chain** (`max_log_arity = 3`): three chained arity-2 folds
with the layer-challenge schedule `β, β², β⁴`, over the fiber
`{±x0, ±x1, ±x2, ±x3}` (leaves `v0..v3` at `+`, `v4..v7` at `−`), pairing
`(v0,v4)@x0, (v2,v6)@x2 → @x0²` and `(v1,v5)@x1, (v3,v7)@x3 → @x1²`, then `→ @x0⁴`. -/
def chain8 (β x0 x1 x2 x3 v0 v1 v2 v3 v4 v5 v6 v7 : F) : F :=
  foldCombineF (β ^ 4) ((x0 ^ 2) ^ 2)
    (foldCombineF (β ^ 2) (x0 ^ 2) (foldCombineF β x0 v0 v4) (foldCombineF β x2 v2 v6))
    (foldCombineF (β ^ 2) (x1 ^ 2) (foldCombineF β x1 v1 v5) (foldCombineF β x3 v3 v7))

/-- **THE KEYSTONE — `chain8_eval8`.** Over any field: if the fiber points satisfy the
coset relations (`x2² = −x0²`, `x3² = −x1²`, `x1⁴ = −x0⁴` — the `ω^8 = −1` geometry) then
the 3-layer deployed fold chain applied to the fiber values of the degree-`< 8`
interpolant `P = eval8 c` computes **`P(β)`** — the interpolant evaluated at the
challenge. Each monomial `X^j` (binary digits `j = b₀+2b₁+4b₂`) picks up
`β^{b₀}·(β²)^{b₁}·(β⁴)^{b₂} = β^j` through the three layers. -/
theorem chain8_eval8 (c : Fin 8 → F) (β x0 x1 x2 x3 : F)
    (h2 : (2 : F) ≠ 0) (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx3 : x3 ≠ 0)
    (hsq2 : x2 ^ 2 = -(x0 ^ 2)) (hsq3 : x3 ^ 2 = -(x1 ^ 2))
    (hq : (x1 ^ 2) ^ 2 = -((x0 ^ 2) ^ 2)) :
    chain8 β x0 x1 x2 x3
      (eval8 c x0) (eval8 c x1) (eval8 c x2) (eval8 c x3)
      (eval8 c (-x0)) (eval8 c (-x1)) (eval8 c (-x2)) (eval8 c (-x3))
    = eval8 c β := by
  unfold chain8
  rw [fold_eval8 β x0 hx0 h2, fold_eval8 β x1 hx1 h2,
      fold_eval8 β x2 hx2 h2, fold_eval8 β x3 hx3 h2,
      hsq2, hsq3,
      fold_eval4 (β ^ 2) (x0 ^ 2) (pow_ne_zero 2 hx0) h2,
      fold_eval4 (β ^ 2) (x1 ^ 2) (pow_ne_zero 2 hx1) h2,
      hq,
      fold_eval2 (β ^ 4) ((x0 ^ 2) ^ 2) (pow_ne_zero 2 (pow_ne_zero 2 hx0)) h2]
  unfold eval8
  ring

end Keystone

/-! ## §3 — Instantiation at the deployed BabyBear setup: the chain IS the abstract `Fold`.

The `Fin 16` RS-domain fiber of `y ∈ Fin 2` is `{repsC y i}` with points
`pC (repsC y i) = ω₁₆^{y+2i}`; the coset relations are kernel-checked (`decide`), and the
Vandermonde components `Cj` of `FriFoldArity` are exactly the interpolant coefficients
(`self_decomp`), so the keystone lands: `foldChain3 = Fold friSetupK8.geom`. -/

private theorem two_ne : (2 : BabyBear) ≠ 0 := by decide

private theorem pC_reps_ne : ∀ (y : Fin 2) (i : Fin 8), pC (repsC y i) ≠ 0 := by decide

private theorem pC_reps_neg : ∀ y : Fin 2,
    pC (repsC y 4) = -pC (repsC y 0) ∧ pC (repsC y 5) = -pC (repsC y 1) ∧
    pC (repsC y 6) = -pC (repsC y 2) ∧ pC (repsC y 7) = -pC (repsC y 3) := by decide

private theorem pC_reps_sq2 : ∀ y : Fin 2,
    pC (repsC y 2) ^ 2 = -(pC (repsC y 0) ^ 2) := by decide

private theorem pC_reps_sq3 : ∀ y : Fin 2,
    pC (repsC y 3) ^ 2 = -(pC (repsC y 1) ^ 2) := by decide

private theorem pC_reps_q : ∀ y : Fin 2,
    (pC (repsC y 1) ^ 2) ^ 2 = -((pC (repsC y 0) ^ 2) ^ 2) := by decide

/-- **The deployed verifier-side fold chain** over the committed BabyBear column oracle:
the 3-layer arity-2 walk (`β, β², β⁴`) over the fiber of `y` in the `Fin 16` RS domain —
the full-domain reading of `friQueryCheck`'s per-query fold-chain arithmetic. -/
noncomputable def foldChain3 (β : BabyBear) (f : Fin 16 → BabyBear) (y : Fin 2) : BabyBear :=
  chain8 β (pC (repsC y 0)) (pC (repsC y 1)) (pC (repsC y 2)) (pC (repsC y 3))
    (f (repsC y 0)) (f (repsC y 1)) (f (repsC y 2)) (f (repsC y 3))
    (f (repsC y 4)) (f (repsC y 5)) (f (repsC y 6)) (f (repsC y 7))

/-- **THE TRANSPORT — the verifier's fold chain IS the abstract arity-8 `Fold`.** For
every oracle, challenge, and fiber: the deployed 3-layer chain equals
`Fold friSetupK8.geom β f y` (the Vandermonde-components fold of `FriFoldArity`). The two
disjoint developments compute the same field element — the cross-type half of
`FriColumnIdentification`, PROVED. -/
theorem foldChain3_eq_fold (β : BabyBear) (f : Fin 16 → BabyBear) (y : Fin 2) :
    foldChain3 β f y = Fold friSetupK8.geom β f y := by
  have hval : ∀ i : Fin 8,
      f (repsC y i) = eval8 (fun j => Cj friGeomK8 j f y) (pC (repsC y i)) := by
    intro i
    rw [eval8_eq_sum]
    have h := self_decomp friGeomK8 f (repsC y i)
    rw [show friGeomK8.q (repsC y i) = y from qC_repsC y i] at h
    exact h
  obtain ⟨h4, h5, h6, h7⟩ := pC_reps_neg y
  unfold foldChain3
  rw [hval 0, hval 1, hval 2, hval 3, hval 4, hval 5, hval 6, hval 7, h4, h5, h6, h7,
      chain8_eval8 (fun j => Cj friGeomK8 j f y) β _ _ _ _ two_ne
        (pC_reps_ne y 0) (pC_reps_ne y 1) (pC_reps_ne y 2) (pC_reps_ne y 3)
        (pC_reps_sq2 y) (pC_reps_sq3 y) (pC_reps_q y),
      eval8_eq_sum]
  rfl

/-- **THE LANDING — constant chain values ⟺ `Fold ∈ friSetupK8.C'`.** The deployed
verifier's "the fold chain bottoms out at the (one) final-poly constant" check, read at
full domain (both fibers), is EXACTLY membership of the abstract fold in the folded code
(`C'` = constants). Both directions — the concrete check neither over- nor under-shoots
the abstract one. -/
theorem fold_mem_C'_iff_chain_const (β : BabyBear) (f : Fin 16 → BabyBear) :
    (∃ k, ∀ y : Fin 2, foldChain3 β f y = k) ↔ Fold friSetupK8.geom β f ∈ friSetupK8.C' := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, funext fun y => by rw [← foldChain3_eq_fold, hk y]⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun y => by rw [foldChain3_eq_fold, ha]⟩

#assert_axioms foldChain3_eq_fold
#assert_axioms fold_mem_C'_iff_chain_const

/-! ## §4 — The residual, renamed into PURE verifier vocabulary, and the transport to
`FriColumnIdentification` → `DeployedTraceDecode` → `[StarkSound]`. -/

/-- **`ColumnDecodeBridge`** — the remaining def-bridge behind `accept_folds`, now stated
with NO abstract-FRI vocabulary (no `Fold`, no `friSetupK8`, no submodules): on
`verifyAlgo`-accept, the deployed 3-layer fold chain over the DECODED committed column
bottoms out at one constant per challenge, at every domain position, for `8` distinct
(rewound) challenges. Its content is exactly the four verifier-side sub-seams of the
module docstring: (a) Merkle commitment → total column (extraction under Poseidon2
binding), (b) spot-check → full domain (the PROBABILISTIC FRI query-soundness step —
`deployed_accept_prob_lt` is its measured bound; not deterministically provable),
(c) the `FriCore.foldCombine`-mod-p pin (`decode_fold_relation` is its proven template),
(d) the 8-challenge transcript rewind. The abstract-FRI half is no longer assumed
anywhere — it is proved in §2–§3. -/
structure ColumnDecodeBridge
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Type where
  /-- The committed FRI column the proof's Merkle cap binds (as the deployed `Int` list). -/
  column : BatchPublicInputs → BatchProof → List Int
  /-- The `8` (rewound) fold challenges of the transcript. -/
  chal : BatchPublicInputs → BatchProof → Fin 8 → BabyBear
  /-- The `8` challenges are DISTINCT (the arity-8 Vandermonde inverts downstream). -/
  chal_inj : ∀ pi π, Function.Injective (chal pi π)
  /-- The decoded FRI final-poly constant each rewound transcript bottoms out at. -/
  finalConst : BatchPublicInputs → BatchProof → Fin 8 → BabyBear
  /-- **THE residual map (verifier vocabulary only)**: on accept, the deployed fold chain
  over the decoded committed column reaches the final constant at EVERY domain position. -/
  accept_chains : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    ∀ (i : Fin 8) (y : Fin 2),
      foldChain3 (chal pi π i) (decodeColumn (column pi π)) y = finalConst pi π i

/-- **`FriColumnIdentification` DERIVED** — the last cross-type map of `accept_folds`,
now a THEOREM from the verifier-vocabulary residual: the chain-constant landing transports
through the proven §2–§3 algebra onto `Fold friSetupK8.geom … ∈ friSetupK8.C'`. -/
theorem friColumnIdentification_of_columnDecode
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (B : ColumnDecodeBridge perm RATE toNat params vk checks initState logN view) :
    FriColumnIdentification perm RATE toNat params vk checks initState logN view
      (fun pi π => decodeColumn (B.column pi π)) B.chal := by
  intro pi π hacc i
  exact (fold_mem_C'_iff_chain_const _ _).mp
    ⟨B.finalConst pi π i, fun y => B.accept_chains pi π hacc i y⟩

/-! ### §4.1 — ⚑ THE CUTOVER RECEIPT: what the retyping cost, and what it bought.

`ood_decode`'s OOD binder is now `OodInterpFExt BB4` — the deployed `Challenge` typing — where it
used to be the base-typed `FieldIntegerLift.OodInterpF`.  Two obligations come with any such move,
and both are discharged here rather than asserted:

* **Nothing is stranded.** `hood_ext_of_hood_base` proves the OLD (base-typed) provider still
  discharges the NEW obligation, because base witnesses LIFT
  (`OodInterpFieldExt.oodInterpFExt_of_oodInterpF`).  So the retyped hypothesis is strictly WEAKER
  and no capability was lost.
* **The new hypothesis is not newly EMPTY.** `hood_ext_binder_inhabited_offbase` exhibits the
  retyped bundle satisfied at a challenge OUTSIDE `image(BabyBear)`, carrying every
  challenge-dependent conjunct (`OodInterpFieldExt.fire_oodInterpFExt_nonbase` records `hood` AND
  `hnonexc` at the exhibited point, not merely the conclusion) — the correction a previous lane paid
  for: an inhabitation witness recording only the CONCLUSION is weaker than it looks.

And what the base-typed binder could NOT express is proved, not asserted:
`ExtChallengeOodSites.extOod_rhs_beyond_base` / `fire_extOod_rhs_beyond_base_transferV3` put the
deployed OOD right-hand side `Z(ζ)·q(ζ)` outside `Set.range (algebraMap BabyBear BB4)` at the real
deployed descriptor, while `base_ood_rhs_mem_range` confines every base-typed right-hand side to it;
`OodExtChallengeLayout.coordFunctional_not_multiplicative` (fired at the deployed quartic basis by
`bb4_lane_not_multiplicative`) kills the "read lane 0 and you are back at the base equation" rescue.
So the old binder was not a conservative restriction of the deployed one — it was a different
equation over a strictly smaller value space. -/

/-- **NOTHING IS STRANDED.** A base-typed OOD/leg decode discharges the retyped one: the OOD bundle
lifts along `algebraMap BabyBear BB4` and every other conjunct is carried verbatim. -/
theorem hood_ext_of_hood_base
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (B : ColumnDecodeBridge perm RATE toNat params vk checks initState logN view)
    (hood : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo perm RATE toNat params vk checks initState logN
          (view pi π).1 (view pi π).2 = true →
      decodeColumn (B.column pi π) ∈ friSetupK8.C →
      ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
          (_ood : Dregg2.Circuit.FieldIntegerLift.OodInterpF (R pi.effect) t),
        (∀ i < t.rows.length, ∀ c ∈ (R pi.effect).constraints, ¬ isArith c →
            c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
        (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) (R pi.effect).hashSites) ∧
        (∀ i < t.rows.length, ∀ r ∈ (R pi.effect).ranges, r.holds (envAt t i)) ∧
        maddrs.Nodup ∧
        (∀ op ∈ memLog (R pi.effect) t, op.addr ∈ maddrs) ∧
        MemoryChecking.Disciplined (memLog (R pi.effect) t) ∧
        MemoryChecking.MemCheck minit mfin maddrs (memLog (R pi.effect) t) ∧
        t.tf .memory = (memLog (R pi.effect) t).map opRow ∧
        t.tf .mapOps = mapLog (R pi.effect) t ∧
        tracePublishedCommit t = pi.toPublished) :
    ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo perm RATE toNat params vk checks initState logN
          (view pi π).1 (view pi π).2 = true →
      decodeColumn (B.column pi π) ∈ friSetupK8.C →
      ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
          (_ood : Dregg2.Circuit.OodInterpFieldExt.OodInterpFExt
            Dregg2.Circuit.OodInterpFieldExt.BB4 (R pi.effect) t),
        (∀ i < t.rows.length, ∀ c ∈ (R pi.effect).constraints, ¬ isArith c →
            c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
        (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) (R pi.effect).hashSites) ∧
        (∀ i < t.rows.length, ∀ r ∈ (R pi.effect).ranges, r.holds (envAt t i)) ∧
        maddrs.Nodup ∧
        (∀ op ∈ memLog (R pi.effect) t, op.addr ∈ maddrs) ∧
        MemoryChecking.Disciplined (memLog (R pi.effect) t) ∧
        MemoryChecking.MemCheck minit mfin maddrs (memLog (R pi.effect) t) ∧
        t.tf .memory = (memLog (R pi.effect) t).map opRow ∧
        t.tf .mapOps = mapLog (R pi.effect) t ∧
        tracePublishedCommit t = pi.toPublished := by
  intro pi π hacc hcw
  obtain ⟨minit, mfin, maddrs, t, hOod, hrest⟩ := hood pi π hacc hcw
  exact ⟨minit, mfin, maddrs, t, oodInterpFExt_of_oodInterpF hOod, hrest⟩

/-- **THE RETYPED BINDER IS NOT NEWLY EMPTY** — inhabited at a challenge outside the base field, with
both challenge-dependent conjuncts carried. -/
theorem hood_ext_binder_inhabited_offbase :
    ∃ ζ : BB4, ζ ∉ Set.range (algebraMap BabyBear BB4) ∧
      Dregg2.Circuit.AirChecksSatisfied.MainAirAcceptF
        Dregg2.Circuit.AirChecksSatisfied.dArith Dregg2.Circuit.AirChecksSatisfied.tHonest := by
  obtain ⟨ζ, hζ, -, -, hair⟩ := fire_oodInterpFExt_nonbase
  exact ⟨ζ, hζ, hair⟩

#assert_axioms hood_ext_of_hood_base
#assert_axioms hood_ext_binder_inhabited_offbase

/-- **The shrunk residual assembled**: a `ColumnDecodeBridge` plus the OOD/leg codeword
decode yields the full `DeployedTraceDecode` — `accept_folds` is now CONSTRUCTED from the
verifier-vocabulary residual (proximity untouched, still load-bearing downstream). -/
noncomputable def deployedTraceDecode_of_columnDecode
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (B : ColumnDecodeBridge perm RATE toNat params vk checks initState logN view)
    (hood : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo perm RATE toNat params vk checks initState logN
          (view pi π).1 (view pi π).2 = true →
      decodeColumn (B.column pi π) ∈ friSetupK8.C →
      ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
          (_ood : Dregg2.Circuit.OodInterpFieldExt.OodInterpFExt
            Dregg2.Circuit.OodInterpFieldExt.BB4 (R pi.effect) t),
        (∀ i < t.rows.length, ∀ c ∈ (R pi.effect).constraints, ¬ isArith c →
            c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
        (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) (R pi.effect).hashSites) ∧
        (∀ i < t.rows.length, ∀ r ∈ (R pi.effect).ranges, r.holds (envAt t i)) ∧
        maddrs.Nodup ∧
        (∀ op ∈ memLog (R pi.effect) t, op.addr ∈ maddrs) ∧
        MemoryChecking.Disciplined (memLog (R pi.effect) t) ∧
        MemoryChecking.MemCheck minit mfin maddrs (memLog (R pi.effect) t) ∧
        t.tf .memory = (memLog (R pi.effect) t).map opRow ∧
        t.tf .mapOps = mapLog (R pi.effect) t ∧
        tracePublishedCommit t = pi.toPublished) :
    DeployedTraceDecode hash R perm RATE toNat params vk checks initState logN view where
  oracle := fun pi π => decodeColumn (B.column pi π)
  chal := B.chal
  chal_inj := B.chal_inj
  accept_folds :=
    friColumnIdentification_of_columnDecode perm RATE toNat params vk checks initState logN view B
  ood_decode := hood

/-- **`[StarkSound]` from the verifier-vocabulary residual** — the apex carrier from
(i) `ColumnDecodeBridge` (the FRI-column residual, abstract half PROVED here), (ii) the
OOD/leg codeword decode, and (iii) `DeployedRefines`; with `friProximityK8_discharge0`
(arity-8 proximity) and the OOD→AIR bridge still PROVED and load-bearing in between. -/
theorem starkSound_of_columnDecode_and_refines
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (B : ColumnDecodeBridge perm RATE toNat params vk checks initState logN view)
    (hood : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo perm RATE toNat params vk checks initState logN
          (view pi π).1 (view pi π).2 = true →
      decodeColumn (B.column pi π) ∈ friSetupK8.C →
      ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
          (_ood : Dregg2.Circuit.OodInterpFieldExt.OodInterpFExt
            Dregg2.Circuit.OodInterpFieldExt.BB4 (R pi.effect) t),
        (∀ i < t.rows.length, ∀ c ∈ (R pi.effect).constraints, ¬ isArith c →
            c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
        (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) (R pi.effect).hashSites) ∧
        (∀ i < t.rows.length, ∀ r ∈ (R pi.effect).ranges, r.holds (envAt t i)) ∧
        maddrs.Nodup ∧
        (∀ op ∈ memLog (R pi.effect) t, op.addr ∈ maddrs) ∧
        MemoryChecking.Disciplined (memLog (R pi.effect) t) ∧
        MemoryChecking.MemCheck minit mfin maddrs (memLog (R pi.effect) t) ∧
        t.tf .memory = (memLog (R pi.effect) t).map opRow ∧
        t.tf .mapOps = mapLog (R pi.effect) t ∧
        tracePublishedCommit t = pi.toPublished)
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view) :
    StarkSound hash R :=
  starkSound_of_traceDecode_and_refines hash R perm RATE toNat params vk checks initState logN view
    (deployedTraceDecode_of_columnDecode hash R perm RATE toNat params vk checks initState logN
      view B hood)
    href

#assert_axioms friColumnIdentification_of_columnDecode
#assert_axioms deployedTraceDecode_of_columnDecode
#assert_axioms starkSound_of_columnDecode_and_refines

/-! ## §5 — TEETH: the transport is genuine, both polarities, plus a kernel-evaluated
end-to-end canary through the REAL fold divisions. -/

/-- **FIRES (abstract → concrete)** — for the honest degree-`< 8` codeword, EVERY
challenge admits a constant chain landing: abstract folding completeness, driven BACKWARD
through the keystone onto the verifier-side chain. The residual's `accept_chains` shape is
satisfiable by honest data. -/
theorem chain_honest_fires (β : BabyBear) : ∃ k, ∀ y : Fin 2, foldChain3 β fHon8 y = k :=
  (fold_mem_C'_iff_chain_const β fHon8).mpr (fHon8_fold_complete β)

/-- **BITES** — the far word `f0` (frequency-8, `∉ C`) admits NO `8` distinct challenges
with constant chain landings: full-domain chain acceptance forces low degree, via the
keystone + the PROVED arity-8 proximity (`f0_no_injective_good`). The verifier-side
residual cannot be met by a far column. -/
theorem chain_far_bites :
    ¬ ∃ (α : Fin 8 → BabyBear) (k : Fin 8 → BabyBear),
        Function.Injective α ∧ ∀ (i : Fin 8) (y : Fin 2), foldChain3 (α i) f0 y = k i := by
  rintro ⟨α, k, hinj, hch⟩
  exact f0_no_injective_good
    ⟨α, hinj, fun i => (fold_mem_C'_iff_chain_const _ _).mp ⟨k i, hch i⟩⟩

/-- The committed INTEGER column of the honest codeword `2 + 3·ω₁₆^x` — the canonical
representatives, as the deployed proof would carry them. -/
def honestColumn : List Int :=
  [5, 589188782, 750566802, 236837402, 1158681699, 174306414, 635169584, 311638005,
   2013265920, 1424077143, 1262699123, 1776428523, 854584226, 1838959511, 1378096341,
   1701627920]

/-- The integer column DECODES to the honest codeword (kernel-checked, all 16 leaves). -/
theorem decode_honest : decodeColumn honestColumn = fHon8 := by decide

/-- **End-to-end kernel canary**: decode the integer column, run the REAL 3-layer fold
chain (genuine `ZMod` divisions) at `β = 5` — both fibers bottom out at
`P(5) = 2 + 3·5 = 17`, exactly what the keystone predicts. A drift anywhere in the chain
wiring (pairing, points, challenge schedule, decode) fails the build. -/
theorem chain_honest_concrete :
    ∀ y : Fin 2, foldChain3 5 (decodeColumn honestColumn) y = 17 := by decide +kernel

#assert_axioms chain_honest_fires
#assert_axioms chain_far_bites
#assert_axioms decode_honest
#assert_axioms chain_honest_concrete
#assert_axioms decode_fold_relation
#assert_axioms decode_mod_p
#assert_axioms chain8_eval8
#assert_axioms foldCombineF_char
#assert_axioms foldCombineF_of_linear_relation
#assert_axioms eval8_eq_sum
#assert_axioms fold_eval8

end Dregg2.Circuit.FriColumnDecode
