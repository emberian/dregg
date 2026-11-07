/-
# `Dregg2.Crypto.Poseidon2RomInstantiation` — ⚑ THE ONE CENTRAL Poseidon2-is-a-keyed-random-oracle
assumption, with BOTH faces of the deployed commitment — BINDING (collision-resistance) and HIDING —
reduced to it, at the EXACT deployed cardinalities.

## The scatter this centralizes

Before this file the ROM tower named its one idealization TWICE, in two different registers:

  * **hiding** named it in Lean (`Poseidon2RomHidingInstantiation.RomFaithfulHiding` /
    `Poseidon2RandomOracleInstantiation`, per adversary, at the deployed cardinalities); while
  * **collision-resistance** carried the SAME idealization as PROSE ONLY (`RomCarrierSites` header:
    "a deliberate, labelled idealisation … NOT a derivation") — and its idealization lives at the
    ASYMPTOTIC digest width `Fin (2 ^ l)`, which equals the deployed BabyBear felt count at NO `l`
    (`mirrorFamily_card_never_deployed`; `babyBearP` is odd).

So the tower rested on one Lean-named assumption beside one prose one — morally identical, unbound.
This file gives the ONE central Lean name and reduces BOTH faces to it.

## The construction

  * **§1 `KeyedRomFaithful H₀ w`** — the generic central predicate, PER EXPERIMENT: for a two-world
    observable `w : Bool → (D → R) → Ω → Bool` (world bit, oracle, auxiliary sample), the two-world
    advantage at the FIXED oracle `H₀` is at most the advantage when the oracle is SAMPLED —
    "the fixed hash serves this experiment no better than a fresh random oracle would". The ROM
    heuristic stated as the inequality it actually is; a `def`/hypothesis, NEVER an `axiom`.
  * **§2 `Poseidon2IsKeyedRandomOracle D w`** — ⚑⚑ THE CENTRAL NAMED ASSUMPTION, at the deployed
    object: `KeyedRomFaithful (deployedSpongeOracle D) w`. The oracle IS the deployed blinded-span
    commitment map (`deployedSpongeOracle_spec` pins it `rfl`-tight to
    `wideHash (tagCode ‖ span_digest8 ‖ C_T ‖ BLINDING ‖ 0)` decoded), over the KEYED
    (blinding-separated) domain `Span × Blind`, at the exact deployed cardinalities — blinding
    literally `Fin 2013265921`, digests `2013265921^8` — fixing on the collision face the
    asymptotic-width trap the prose version carried.
  * **§3 HIDING FROM IT.** `hidingObservable A` is the hiding experiment as an observable, and the
    bridge is DEFINITIONAL: `fixedWorldAdv/romWorldAdv` at it ARE `fixedHidingAdv/hidingAdv`
    (`rfl`), so the central assumption is EQUIVALENT to the previously named hiding assumption
    (`poseidon2KeyedRO_iff_hidingInstantiation`) — a re-expression, not a second floor — and the
    deployed hiding bound `≤ 2Q/2013265921` follows (`deployed_hiding_of_poseidon2KeyedRO`).
  * **§4 BINDING FROM IT.** `collisionObservable M` embeds the collision game as the same shape
    (world `false` ≡ reject, world `true` ≡ the collision indicator): the fixed-oracle advantage is
    the deployed-sponge collision INDICATOR, the sampled-oracle advantage is `winProb (collWin M)`,
    and the PROVED birthday floor (`RomQueryFloor.birthday_bound`, untouched) closes the reduction:
    under the central assumption a `Q`-query forger's deployed collision indicator is
    `≤ (Q² + 1)/2013265921^8` (`deployed_binding_of_poseidon2KeyedRO`); since an indicator is 0-or-1,
    for any `Q` under the birthday bar the forger exhibits NO collision of the deployed commitment
    map at all (`deployed_noCollision_of_poseidon2KeyedRO`), i.e. its output pair is NOT an
    equivocation — deployed binding (`deployed_blindedSpan_binding_of_poseidon2KeyedRO`).
  * **§5 BOTH POLES, ON BOTH FACES.** Satisfiable: the constant hiding distinguisher and the
    diagonal (equal-pair) forger are both faithful at EVERY deployed commitment. Refuted universal:
    the `∀`-form of the central assumption is FALSE on the hiding face (transported: the leak-sponge
    table-baker, fixed advantage `1`, ROM advantage `0`) AND on the collision face
    (`poseidon2KeyedRO_not_universal_collision`: at the leak sponge a 0-query fixed pair collides
    with fixed-oracle certainty but sampled-oracle probability exactly `1/2013265921^8`). So the
    honest assumption is PER-EXPERIMENT ("uses the sponge generically") — any lane upgrading it to
    `∀ w` is asserting a shape refuted here twice.

## HONEST HEADER — what is PROVED vs what is ASSUMED

This file NAMES and CENTRALIZES the idealization; it does NOT discharge it. Poseidon2-is-a-keyed-RO
(`Poseidon2IsKeyedRandomOracle`, per experiment) stays the ONE named floor the whole ROM tower rests
on — not dischargeable without idealization (Canetti–Goldreich–Halevi; the §5 refutations are its
finitary shadow, in-tree, on both faces). PROVED (kernel-clean, no assumption): both reductions and
everything under them (the birthday floor and the hiding floor are information-theoretic counting);
the definitional bridges; the concrete-cardinality arithmetic; both poles on both faces. ASSUMED
(the one named residual): the central instantiation itself, per experiment. Nothing here says
anything about the real hash bytes beyond that named instantiation.

ADDITIVE, and scope disclosed: every existing collision and hiding theorem is UNCHANGED — the
asymptotic-width keyed-ROM tower (`KeyedRomFloor.keyedRom_hard` → `RomBindingReduction` →
`RomCarrierSites` → the `_binds_rom` sites, which the FRI closure consumes) still stands exactly as
it was, still carrying its prose caveat at its own sites. What THIS file adds beside it is the
deployed-cardinality statement of both faces under the one central name. The collision face here is
the blinded-span commitment map — the SAME deployed object hiding is about, which is exactly what
makes one shared oracle (hence one shared assumption) possible; re-pointing `RomCarrierSites`' other
per-site prose caveats at `KeyedRomFaithful` instances over their own domains is follow-up
(un-additive) rewiring, surfaced, not smuggled.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, NO new `axiom`, no
`native_decide`. The central assumption is a `def` reduced-to. NEW ADDITIVE file; imports read-only.
-/
import Dregg2.Crypto.Poseidon2RomHidingInstantiation
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.Poseidon2RomInstantiation

open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_bot winProb_nonneg winProb_le_one)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomCounting (condProb_cyl_empty)
open Dregg2.Crypto.RomQueryFloor (collWin collWin_pure birthday_bound condProb_two_fresh_eq)
open Dregg2.Crypto.RomCarrierSites (babyBearP babyBearP_pos one_lt_babyBearP)
open Dregg2.Crypto.KeyedRomHidingFloor (HidingDistinguisher QueryHiding acceptProb hidingAdv)
open Dregg2.Crypto.Poseidon2RomHidingInstantiation
open Metatheory.Open.BlindedSpanHiding (BlindedSpanCommitment)

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## §1 — the generic central predicate: a fixed oracle is ROM-faithful FOR AN EXPERIMENT.

An experiment is a two-world observable `w : Bool → (D → R) → Ω → Bool` — world bit, oracle,
auxiliary uniform sample (the challenger's residual randomness: the hidden blinding for hiding,
nothing (`Unit`) for collision). Both faces of the commitment are instances of this one shape, which
is what lets ONE named assumption serve both. -/

section Generic

variable {D R Ω : Type}
variable [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Fintype Ω]

/-- The probability of the observable in world `b` at the FIXED oracle `H₀`: only the auxiliary
sample `ω` is random — the deployed situation, where the sponge is a fixed public function. -/
noncomputable def fixedWorldProb (H₀ : D → R) (w : Bool → (D → R) → Ω → Bool) (b : Bool) : ℝ :=
  (∑ ω : Ω, if w b H₀ ω then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ)

/-- The two-world advantage at the FIXED oracle. -/
noncomputable def fixedWorldAdv (H₀ : D → R) (w : Bool → (D → R) → Ω → Bool) : ℝ :=
  |fixedWorldProb H₀ w false - fixedWorldProb H₀ w true|

/-- The probability of the observable in world `b` when the oracle is SAMPLED (uniformly, AFTER the
experiment is fixed) alongside the auxiliary sample. -/
noncomputable def romWorldProb (w : Bool → (D → R) → Ω → Bool) (b : Bool) : ℝ :=
  (∑ ω : Ω, winProb (fun H : D → R => w b H ω)) / (Fintype.card Ω : ℝ)

/-- The two-world advantage at the SAMPLED oracle. -/
noncomputable def romWorldAdv (w : Bool → (D → R) → Ω → Bool) : ℝ :=
  |romWorldProb w false - romWorldProb w true|

/-- **⚑ `KeyedRomFaithful H₀ w` — the generic central predicate, per experiment.** The fixed hash
`H₀` serves the experiment `w` no better than a freshly sampled oracle would. This is the
random-oracle heuristic stated as the inequality it actually is — a HYPOTHESIS (`def`, never an
`axiom`), reduced to, and REFUTED in its universal form in §5 (a fixed function is public; its
table is available at experiment-design time). -/
def KeyedRomFaithful (H₀ : D → R) (w : Bool → (D → R) → Ω → Bool) : Prop :=
  fixedWorldAdv H₀ w ≤ romWorldAdv w

end Generic

set_option linter.unusedVariables false in
/-- **(CANARY — faithfulness of ONE experiment does not discharge ANOTHER.)** Only `w`'s own named
instantiation connects `w`'s fixed-oracle advantage to the sampled-oracle side; the hypothesis is
PER-EXPERIMENT by construction. If this stops failing, the central assumption has silently become a
blanket `∀ w` — the exact shape §5 refutes. -/
example {D R Ω : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Fintype Ω]
    (H₀ : D → R) (w w' : Bool → (D → R) → Ω → Bool) (h' : KeyedRomFaithful H₀ w') : True := by
  fail_if_success (have : fixedWorldAdv H₀ w ≤ romWorldAdv w := h')
  trivial

/-! ## §2 — ⚑⚑ THE CENTRAL NAMED ASSUMPTION, at the deployed object and deployed cardinalities.

`Span`, `Blind`, `Digest`, `deployedSpongeOracle` are `Poseidon2RomHidingInstantiation`'s — the SAME
deployed types (8-felt spans/digests over `Fin babyBearP`, one-felt blinding) and the SAME `rfl`-pinned
weld to `BlindedSpanCommitment.commitAt`; nothing is re-minted. -/

/-- **⚑⚑⚑ `Poseidon2IsKeyedRandomOracle D w` — THE ONE CENTRAL ASSUMPTION.** The deployed wide
Poseidon2 — as the blinded-span commitment map over the keyed (blinding-separated) domain
`Span × Blind`, at the exact deployed cardinalities — serves the experiment `w` no better than a
sampled keyed random oracle. Per experiment (the `∀ w` strengthening is REFUTED in §5, on BOTH
faces); never an `axiom`. Binding (§4) and hiding (§3) both reduce to instances of THIS predicate:
it is the single named floor the ROM tower rests on. -/
def Poseidon2IsKeyedRandomOracle {Ω : Type} [Fintype Ω] (D : BlindedSpanCommitment)
    (w : Bool → (Span × Blind → Digest) → Ω → Bool) : Prop :=
  KeyedRomFaithful (deployedSpongeOracle D) w

/-! ## §3 — HIDING reduces to the central assumption (definitional bridge). -/

/-- The deployed hiding experiment, as an observable: the auxiliary sample is the hidden blinding,
and the verdict is the distinguisher's — on the challenge `H (msgAt b, r)`. -/
def hidingObservable (A : HidingDistinguisher Span Blind Digest) :
    Bool → (Span × Blind → Digest) → Blind → Bool :=
  fun b H r => A.accept H r (H (A.msgAt b, r))

/-- The fixed-oracle world probability of the hiding observable IS `fixedAcceptProb` — definitional. -/
theorem fixedWorldProb_hiding (H₀ : Span × Blind → Digest)
    (A : HidingDistinguisher Span Blind Digest) (b : Bool) :
    fixedWorldProb H₀ (hidingObservable A) b = fixedAcceptProb H₀ A b := rfl

/-- The sampled-oracle world probability of the hiding observable IS `acceptProb` — definitional. -/
theorem romWorldProb_hiding (A : HidingDistinguisher Span Blind Digest) (b : Bool) :
    romWorldProb (hidingObservable A) b = acceptProb A b := rfl

/-- The fixed-oracle advantage of the hiding observable IS `fixedHidingAdv` — definitional. -/
theorem fixedWorldAdv_hiding (H₀ : Span × Blind → Digest)
    (A : HidingDistinguisher Span Blind Digest) :
    fixedWorldAdv H₀ (hidingObservable A) = fixedHidingAdv H₀ A := rfl

/-- The sampled-oracle advantage of the hiding observable IS `hidingAdv` — definitional. -/
theorem romWorldAdv_hiding (A : HidingDistinguisher Span Blind Digest) :
    romWorldAdv (hidingObservable A) = hidingAdv A := rfl

/-- **⚑⚑ THE HIDING FACE IS AN INSTANCE OF THE CENTRAL ASSUMPTION — equivalence, not implication.**
The central assumption at the hiding observable IS the previously named per-adversary hiding
assumption. So the tower's hiding face now rests on `Poseidon2IsKeyedRandomOracle`, with the old
name a definitional re-expression — one floor, not two. -/
theorem poseidon2KeyedRO_iff_hidingInstantiation (D : BlindedSpanCommitment)
    (A : HidingDistinguisher Span Blind Digest) :
    Poseidon2IsKeyedRandomOracle D (hidingObservable A)
      ↔ Poseidon2RandomOracleInstantiation D A := by
  constructor
  · intro h
    show fixedHidingAdv (deployedSpongeOracle D) A ≤ hidingAdv A
    rw [← fixedWorldAdv_hiding, ← romWorldAdv_hiding]
    exact h
  · intro h
    show fixedWorldAdv (deployedSpongeOracle D) (hidingObservable A)
        ≤ romWorldAdv (hidingObservable A)
    rw [fixedWorldAdv_hiding, romWorldAdv_hiding]
    exact h

/-- **⚑⚑ DEPLOYED HIDING, FROM THE CENTRAL ASSUMPTION.** Under `Poseidon2IsKeyedRandomOracle` at the
hiding observable, every `Q`-query adversary's two-world span-distinguishing advantage against the
DEPLOYED blinded commitment is `≤ 2·Q / 2013265921` — the proved keyed-ROM hiding floor, inherited
through the one central name, at the deployed cardinalities (the ~31-bit one-felt-blinding budget,
said out loud as before). -/
theorem deployed_hiding_of_poseidon2KeyedRO (D : BlindedSpanCommitment)
    (A : HidingDistinguisher Span Blind Digest) (Q : ℕ) (hA : QueryHiding Q A)
    (hRom : Poseidon2IsKeyedRandomOracle D (hidingObservable A)) :
    fixedHidingAdv (deployedSpongeOracle D) A ≤ 2 * (Q : ℝ) / 2013265921 :=
  deployed_blindedSpan_hiding_of_romInstantiation D A Q hA
    ((poseidon2KeyedRO_iff_hidingInstantiation D A).mp hRom)

/-! ## §4 — BINDING (collision-resistance) reduces to the SAME central assumption.

A collision of `deployedSpongeOracle D` is exactly an EQUIVOCATION of the deployed blinded-span
commitment: two distinct `(span, blinding)` openings with equal commitment digest. The collision
game embeds into the central two-world shape with world `false` ≡ reject and NO auxiliary
randomness (`Ω := Unit`) — at a fixed public sponge the collision game has no residual sample, which
is precisely why the old prose caveat could not literally reuse the hiding predicate; the shared
OBSERVABLE shape is what unifies them. -/

/-- A collision forger against the deployed commitment map: an oracle program over the keyed domain
`Span × Blind` outputting a candidate colliding pair of openings. -/
abbrev CollisionForger : Type :=
  OracleComp (Span × Blind) Digest ((Span × Blind) × (Span × Blind))

/-- The collision game, as an observable: world `false` never accepts, world `true` accepts iff the
forger's output pair is a genuine collision of the oracle. No auxiliary randomness. -/
def collisionObservable (M : CollisionForger) :
    Bool → (Span × Blind → Digest) → Unit → Bool :=
  fun b H _ => b && collWin M H

/-- The fixed-oracle advantage of the collision observable is the collision INDICATOR at the fixed
oracle — `1` if the forger's pair collides there, else `0`. Deterministic, as it must be: a fixed
public sponge leaves the collision game nothing to sample. -/
theorem fixedWorldAdv_collision (H₀ : Span × Blind → Digest) (M : CollisionForger) :
    fixedWorldAdv H₀ (collisionObservable M)
      = if collWin M H₀ then (1 : ℝ) else 0 := by
  have hfalse : fixedWorldProb H₀ (collisionObservable M) false = 0 := by
    simp [fixedWorldProb, collisionObservable]
  have htrue : fixedWorldProb H₀ (collisionObservable M) true
      = if collWin M H₀ then (1 : ℝ) else 0 := by
    simp [fixedWorldProb, collisionObservable]
  rw [fixedWorldAdv, hfalse, htrue]
  split <;> norm_num

/-- The sampled-oracle advantage of the collision observable is the forger's ROM collision
probability — the quantity the PROVED birthday floor bounds. -/
theorem romWorldAdv_collision (M : CollisionForger) :
    romWorldAdv (collisionObservable M) = winProb (collWin M) := by
  have hfalse : romWorldProb (collisionObservable M) false = 0 := by
    simp [romWorldProb, collisionObservable, winProb_bot]
  have htrue : romWorldProb (collisionObservable M) true = winProb (collWin M) := by
    simp [romWorldProb, collisionObservable]
  rw [romWorldAdv, hfalse, htrue, zero_sub, abs_neg, abs_of_nonneg (winProb_nonneg _)]

/-- The deployed digest space has EXACTLY `2013265921^8` elements — the deployed cardinality, where
the prose collision caveat's `Fin (2 ^ l)` matched at no `l`. -/
theorem card_Digest : Fintype.card Digest = babyBearP ^ 8 := by
  rw [Fintype.card_eq_nat_card, Nat.card_fun, Nat.card_fin, Nat.card_fin]

theorem one_lt_card_Digest : 1 < Fintype.card Digest := by
  rw [card_Digest]
  calc 1 < babyBearP := one_lt_babyBearP
    _ ≤ babyBearP ^ 8 := Nat.le_self_pow (by norm_num) _

/-- **⚑⚑ DEPLOYED BINDING, FROM THE CENTRAL ASSUMPTION — through the untouched birthday floor.**
Under `Poseidon2IsKeyedRandomOracle` at the collision observable, a `Q`-query forger's collision
indicator at the DEPLOYED commitment map is at most `(Q² + 1) / 2013265921^8` — the proved
information-theoretic `birthday_bound` transported through the one central name, at the deployed
cardinality (`card_Digest`), with no `Fin (2 ^ l)` mirror anywhere in the chain. What is PROVED:
the reduction and the floor under it. What is ASSUMED: exactly `hRom`. -/
theorem deployed_binding_of_poseidon2KeyedRO (D : BlindedSpanCommitment)
    (M : CollisionForger) (Q : ℕ) (hM : QueryBounded Q M)
    (hRom : Poseidon2IsKeyedRandomOracle D (collisionObservable M)) :
    (if collWin M (deployedSpongeOracle D) then (1 : ℝ) else 0)
      ≤ ((Q : ℝ) * (Q : ℝ) + 1) / (2013265921 : ℝ) ^ 8 := by
  have h2 : fixedWorldAdv (deployedSpongeOracle D) (collisionObservable M)
      ≤ romWorldAdv (collisionObservable M) := hRom
  rw [fixedWorldAdv_collision, romWorldAdv_collision] at h2
  have h3 := birthday_bound (D := Span × Blind) (R := Digest) Q M hM
  have hc : ((Fintype.card Digest : ℕ) : ℝ) = (2013265921 : ℝ) ^ 8 := by
    rw [card_Digest]
    push_cast
    norm_num [Dregg2.Crypto.RomCarrierSites.babyBearP]
  rw [hc] at h3
  exact h2.trans h3

/-- **⚑ THE INDICATOR IS 0-OR-1, SO UNDER THE BIRTHDAY BAR IT IS ZERO: the forger exhibits NO
collision of the deployed commitment map at all.** For every query budget with `Q² + 1` below
`2013265921^8` (i.e. every remotely realistic `Q`), the central assumption forces the deployed
collision indicator strictly below `1`, hence — being an indicator — to `0`. This is deployed
collision-resistance FOR THE GIVEN FORGER, honestly scoped: exactly what "Poseidon2 is a keyed RO
for this experiment" buys, and nothing more. -/
theorem deployed_noCollision_of_poseidon2KeyedRO (D : BlindedSpanCommitment)
    (M : CollisionForger) (Q : ℕ) (hM : QueryBounded Q M)
    (hRom : Poseidon2IsKeyedRandomOracle D (collisionObservable M))
    (hQ : (Q : ℝ) * (Q : ℝ) + 1 < (2013265921 : ℝ) ^ 8) :
    collWin M (deployedSpongeOracle D) = false := by
  cases hcw : collWin M (deployedSpongeOracle D) with
  | false => simp
  | true =>
    have h1 := deployed_binding_of_poseidon2KeyedRO D M Q hM hRom
    rw [hcw, if_pos rfl] at h1
    have hpos : (0 : ℝ) < (2013265921 : ℝ) ^ 8 := by positivity
    rw [le_div_iff₀ hpos, one_mul] at h1
    exact absurd hQ (not_lt.mpr h1)

/-- **⚑⚑ DEPLOYED BINDING, PHRASED AS NON-EQUIVOCATION.** Under the central assumption (and the
birthday bar on `Q`), the pair of openings the forger extracts at the deployed commitment map is
NOT an equivocation: either the two `(span, blinding)` openings coincide, or their commitment
digests differ. Via `deployedSpongeOracle_spec` the digests here are literally
`decodeDigest (wideHash (tagCode ‖ span ‖ C_T ‖ blinding ‖ 0))` — the deployed object, no mirror. -/
theorem deployed_blindedSpan_binding_of_poseidon2KeyedRO (D : BlindedSpanCommitment)
    (M : CollisionForger) (Q : ℕ) (hM : QueryBounded Q M)
    (hRom : Poseidon2IsKeyedRandomOracle D (collisionObservable M))
    (hQ : (Q : ℝ) * (Q : ℝ) + 1 < (2013265921 : ℝ) ^ 8) :
    (M.eval (deployedSpongeOracle D)).1 = (M.eval (deployedSpongeOracle D)).2
      ∨ deployedSpongeOracle D (M.eval (deployedSpongeOracle D)).1
          ≠ deployedSpongeOracle D (M.eval (deployedSpongeOracle D)).2 := by
  have hfalse := deployed_noCollision_of_poseidon2KeyedRO D M Q hM hRom hQ
  by_contra hcon
  push Not at hcon
  have hwin : collWin M (deployedSpongeOracle D) = true := by
    have h1 : decide ((M.eval (deployedSpongeOracle D)).1
        ≠ (M.eval (deployedSpongeOracle D)).2) = true := decide_eq_true hcon.1
    have h2 : decide (deployedSpongeOracle D (M.eval (deployedSpongeOracle D)).1
        = deployedSpongeOracle D (M.eval (deployedSpongeOracle D)).2) = true :=
      decide_eq_true hcon.2
    show (decide ((M.eval (deployedSpongeOracle D)).1 ≠ (M.eval (deployedSpongeOracle D)).2)
        && decide (deployedSpongeOracle D (M.eval (deployedSpongeOracle D)).1
            = deployedSpongeOracle D (M.eval (deployedSpongeOracle D)).2)) = true
    rw [h1, h2]
    rfl
  rw [hfalse] at hwin
  exact Bool.false_ne_true hwin

/-! ## §5 — ⚑ BOTH POLES OF THE CENTRAL ASSUMPTION, ON BOTH FACES. -/

/-- The zero felt. -/
def feltZero : Felt := ⟨0, babyBearP_pos⟩

/-- The one felt. -/
def feltOne : Felt := ⟨1, one_lt_babyBearP⟩

theorem feltZero_ne_feltOne : feltZero ≠ feltOne := by
  intro h
  have hval : (0 : ℕ) = 1 := congrArg Fin.val h
  exact absurd hval (by norm_num)

/-- **(SATISFIABILITY — hiding face.)** The central assumption is inhabited at EVERY deployed
commitment by the constant distinguisher's hiding observable (both advantages `0`) — transported
from the hiding lane's own witness through the definitional bridge. -/
theorem poseidon2KeyedRO_satisfiable_hiding (D : BlindedSpanCommitment) :
    Poseidon2IsKeyedRandomOracle D (hidingObservable (constAdv spanZero spanOne)) :=
  (poseidon2KeyedRO_iff_hidingInstantiation D _).mpr (poseidon2RomInstantiation_satisfiable D)

/-- The diagonal forger: a `0`-query program answering with an EQUAL pair — it never wins anywhere,
so it is faithful everywhere. -/
def diagForger : CollisionForger :=
  OracleComp.pure ((spanZero, feltZero), (spanZero, feltZero))

theorem diagForger_zeroQuery : QueryBounded 0 diagForger := QueryBounded.pure 0 _

/-- **(SATISFIABILITY — collision face.)** The central assumption is inhabited at EVERY deployed
commitment by the diagonal forger's collision observable: fixed advantage `0`, ROM advantage `0`.
So `Poseidon2IsKeyedRandomOracle` is not the empty class on either face. -/
theorem poseidon2KeyedRO_satisfiable_collision (D : BlindedSpanCommitment) :
    Poseidon2IsKeyedRandomOracle D (collisionObservable diagForger) := by
  have hcoll : collWin diagForger = fun _ : Span × Blind → Digest => false := by
    funext H
    unfold diagForger
    rw [collWin_pure]
    simp
  show fixedWorldAdv (deployedSpongeOracle D) (collisionObservable diagForger)
      ≤ romWorldAdv (collisionObservable diagForger)
  rw [fixedWorldAdv_collision, romWorldAdv_collision, hcoll, winProb_bot]
  simp

/-- **⚑ (REFUTATION — hiding face.) THE UNIVERSAL FORM IS FALSE**, transported: the leak-sponge
commitment and the 0-query table-baking distinguisher (fixed advantage `1`, ROM advantage `0`)
refute `∀`-quantified `Poseidon2IsKeyedRandomOracle` at the hiding observable. -/
theorem poseidon2KeyedRO_not_universal_hiding :
    ∃ (D : BlindedSpanCommitment) (A : HidingDistinguisher Span Blind Digest),
      QueryHiding 0 A ∧ ¬ Poseidon2IsKeyedRandomOracle D (hidingObservable A) := by
  obtain ⟨D, A, hQ, hnot⟩ := poseidon2RomInstantiation_not_universal
  exact ⟨D, A, hQ, fun h => hnot ((poseidon2KeyedRO_iff_hidingInstantiation D A).mp h)⟩

/-- The fixed-pair forger: `0` queries, answering with two openings that share a span and differ in
the blinding — a genuine collision of the LEAK sponge (which hands the span back), baked in at
design time. -/
def leakForger : CollisionForger :=
  OracleComp.pure ((spanZero, feltZero), (spanZero, feltOne))

theorem leakForger_zeroQuery : QueryBounded 0 leakForger := QueryBounded.pure 0 _

/-- **⚑ (REFUTATION — collision face.) THE UNIVERSAL FORM IS FALSE HERE TOO.** At the leak-sponge
commitment the fixed-pair forger's collision indicator is `1` at the FIXED oracle, while its
sampled-oracle collision probability is EXACTLY `1/2013265921^8` (< 1) — a fixed public hash's
collisions are available at design time; a sampled oracle's are not. So the central assumption is
PER-EXPERIMENT on the binding face for the same structural reason as on the hiding face, and any
`∀ w` upgrade at the real sponge asserts a shape refuted on BOTH faces. -/
theorem poseidon2KeyedRO_not_universal_collision :
    ∃ (D : BlindedSpanCommitment) (M : CollisionForger),
      QueryBounded 0 M ∧ ¬ Poseidon2IsKeyedRandomOracle D (collisionObservable M) := by
  refine ⟨leakCommitment, leakForger, leakForger_zeroQuery, fun h => ?_⟩
  have hx : ((spanZero, feltZero) : Span × Blind) ≠ (spanZero, feltOne) := by
    intro hEq
    exact feltZero_ne_feltOne (congrArg Prod.snd hEq)
  -- Fixed side: the pair really collides at the leak sponge — indicator `1`.
  have hfix : collWin leakForger (deployedSpongeOracle leakCommitment) = true := by
    unfold leakForger
    rw [collWin_pure, leakOracle_eq]
    simp [hx]
  -- Sampled side: a fixed distinct pair collides with probability exactly `1/|Digest|`.
  have hpred : collWin leakForger
      = fun H : Span × Blind → Digest =>
          decide (H (spanZero, feltZero) = H (spanZero, feltOne)) := by
    funext H
    unfold leakForger
    rw [collWin_pure]
    simp [hx]
  have hrom : winProb (collWin leakForger) = 1 / (Fintype.card Digest : ℝ) := by
    rw [hpred]
    have hk := condProb_two_fresh_eq (D := Span × Blind) (R := Digest) ∅
      (fun _ => Classical.arbitrary Digest) (spanZero, feltZero) (spanZero, feltOne)
      (by simp) (by simp) hx
    rwa [condProb_cyl_empty] at hk
  have h2 : fixedWorldAdv (deployedSpongeOracle leakCommitment) (collisionObservable leakForger)
      ≤ romWorldAdv (collisionObservable leakForger) := h
  rw [fixedWorldAdv_collision, romWorldAdv_collision, hfix, hrom] at h2
  rw [if_pos rfl] at h2
  have hD : (1 : ℝ) < (Fintype.card Digest : ℝ) := by exact_mod_cast one_lt_card_Digest
  have hlt : 1 / (Fintype.card Digest : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]
    exact hD
  linarith

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  fixedWorldProb_hiding,
  romWorldProb_hiding,
  fixedWorldAdv_hiding,
  romWorldAdv_hiding,
  poseidon2KeyedRO_iff_hidingInstantiation,
  deployed_hiding_of_poseidon2KeyedRO,
  fixedWorldAdv_collision,
  romWorldAdv_collision,
  card_Digest,
  one_lt_card_Digest,
  deployed_binding_of_poseidon2KeyedRO,
  deployed_noCollision_of_poseidon2KeyedRO,
  deployed_blindedSpan_binding_of_poseidon2KeyedRO,
  feltZero_ne_feltOne,
  poseidon2KeyedRO_satisfiable_hiding,
  diagForger_zeroQuery,
  poseidon2KeyedRO_satisfiable_collision,
  poseidon2KeyedRO_not_universal_hiding,
  leakForger_zeroQuery,
  poseidon2KeyedRO_not_universal_collision
]

end Dregg2.Crypto.Poseidon2RomInstantiation
