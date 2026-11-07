/-
# `Dregg2.Crypto.KeyedRomFloor` — the KEYED, QUERY-COUNTED collision floor, and the death of the
counterexample that refutes the `IsPolyTime` floor.

## The bug this file answers (proved in-tree, `Exec.SystemRootsBindingReduction` §6)

`sysRoots_floor_polyTime_false_babyBear` proves

    ¬ HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))

i.e. the deployed sponge's collision floor, at the `CostAdversary.IsPolyTime` class, is **FALSE** at
deployed BabyBear parameters. The refutation is the same disease as ArkLib's `KZG.binding`
(`docs/reference/ARKLIB-KZG-VACUITY.md`): `IsPolyTime sz A` reduces to *poly-SIZE answers*
(`CostAdversary.isPolyTime_of_polySize_answers`), because `idAdv` embeds ANY Lean function — a
`Classical.choice` one included — as `.pure (a₀ l i)`, whose whole cost is `sz (a₀ l i)`. So the
`shortCollAdv` that answers each sampled tag with a TWO-LIMB collision (which EXISTS, by pigeonhole,
in the fixed compressing sponge) is in the class and wins with probability `1`. `IsPolyTime` prices
the answer's *size*, never the *difficulty of finding it*, so it cannot separate "writes a short
string" from "finds a collision". Every `_from_polyTime` reduction on the spine inherits this: their
floor hypothesis is refutable, hence they are VACUOUS at deployed parameters.

## The two load-bearing fixes (both required — the counterexample needs both), and where they already live

`Crypto.RomQueryFloor` already carries BOTH, for a random oracle:

  1. **The hash is an ORACLE the adversary QUERIES, cost is QUERY-COUNTED.** `RomOracle.OracleComp` is
     a decision tree that branches only on answers it *asked for*; `QueryBounded Q M` bounds the calls
     along every path; `RomEff F Q` is the class of raw adversaries that FACTOR THROUGH such a tree.
     The collision is not a `.pure` value handed back — it must be found through `query` nodes.
  2. **KEYED — the key/oracle sampled AFTER the adversary is fixed.** In `romCollisionGame F` the
     *instance* is the sampled oracle `H`; `RomEff`'s tree `M` is fixed BEFORE `H`. A `Classical.choice`
     answerer would have to know a collision of `H` without querying it — and
     `RomOracle.OracleComp.eval_congr_of_agree_on_queried` proves an oracle program's output is a
     function of the answers it *received* and of nothing else. So it cannot bake a collision in.

`RomQueryFloor.choiceAdv_not_romEff` PROVES the collision-answerer is excluded; `romCollision_hard`
PROVES the floor (the birthday bound, no assumption under it); `binaryRom_verdict` prices both poles.

## What THIS file adds

The deployed floor is over a KEYED family (`spongeFamily D` is keyed by its domain-separation tag).
This file gives the keyed presentation of `RomQueryFloor` — the collision game over the tag-separated
domain `Key × Input` — and, crucially, the two theorems that are the ACCEPTANCE TEST for the fix:

  * **§3 (a) THE FULL-ORACLE CHOICE ANSWERER IS EXCLUDED.** `not_keyedRomEff_of_not_negl`: any
    adversary whose advantage is not negligible is outside `KeyedRomEff`. Applied to the
    `Classical.choice` answerer (advantage `1` at a compressing family), it is EXCLUDED — the direct
    analogue of `shortCollAdv`'s exclusion. The refutation strategy of
    `sysRoots_floor_polyTime_false_babyBear` cannot produce a member of the fixed class.
  * **§3 (b) THE FIXED SHORT-COLLISION ANSWERER IS DEFANGED.** The sharper mirror. The *exact* shape
    that refutes the `IsPolyTime` floor — a `.pure` leaf answering with a FIXED short collision — IS
    admitted by `KeyedRomEff` (it is a `0`-query tree), but over the SAMPLED oracle a fixed pair
    collides with probability only `1/|R|` (`fixedPairAdv_gameAdv_eq`), which is NEGLIGIBLE
    (`fixedPairAdv_negl`). So the adversary that wins with probability `1` against the *fixed* sponge
    wins only negligibly against the *sampled* oracle. Sampling the key after the adversary is exactly
    what collapses its advantage. It does NOT refute the keyed/query-counted floor.

Together these are the counterexample dying: neither the excluded full-oracle answerer nor the
admitted fixed answerer refutes the fixed floor, and §2's `keyedRom_hard` PROVES the floor holds.

## Both poles, at the fixed model (§4)

`keyedRom_top_false` — the UNRESTRICTED floor at the same keyed game is FALSE (compressing pigeonhole),
so `KeyedRomEff` is not `⊤` in disguise. `twoPointKeyed_in_keyedRomEff` + `twoPointKeyed_gameAdv_pos`
— a real two-query adversary is in the class and wins with positive advantage, so it is not `⊥`.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`. `Classical.choice` enters only via the excluded full-oracle answerer.
-/
import Dregg2.Crypto.RomQueryFloor
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.KeyedRomFloor

open Dregg2.Crypto.ConcreteSecurity (Ensemble Negl PolyBounded negl_two_pow not_negl_one)
open Dregg2.Crypto.FloorGames
  (Game Adversary Hard gameAdv gameAdv_mem_unit solvableFrac choiceAdv choiceAdv_gameAdv
   hard_top_iff_solvableFrac_negl not_hard_top_of_always_solvable)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomCounting (condProb_cyl_empty)
open Dregg2.Crypto.RomQueryFloor
  (RomFamily romCollisionGame RomComp romAdv RomEff collWin collWin_pure romAdv_hit
   romCollision_hard romCollision_top_false romCollision_always_solvable choiceAdv_not_romEff
   condProb_two_fresh_eq twoPointComp twoPointComp_bounded twoPointComp_collWin
   twoPointAdv_in_romEff twoPointAdv_gameAdv_eq twoPointAdv_gameAdv_pos)

set_option autoImplicit false

/-! ## §1 — the keyed family, its collision game, and the query-bounded class.

The keying is the standard keyed-from-unkeyed model, exactly as `SpongeCarrierReduction.SpongeKeyed`
uses it: an unkeyed fixed hash lets an adversary hardcode a known collision, so the collision game
must sample something. Here what is sampled is the ORACLE (the random-oracle idealization of the
deployed sponge), and the domain is the TAG-SEPARATED input space `Key × Input`, so a collision is
between two distinct tagged messages — the object the domain-separated sponge is supposed to bind. -/

/-- **A KEYED RANDOM-ORACLE FAMILY.** At each security parameter: a finite tag/key space, a finite
input domain, and a finite range. The idealized keyed hash is a uniformly sampled function on the
tag-separated domain `Key l × D l`. No hash function is named — in the random oracle model the sampled
function IS the object, and the tag is a coordinate of its domain (domain separation). -/
structure KeyedRomFamily where
  /-- The domain-separation tag/key space at parameter `l`. -/
  Key : ℕ → Type
  /-- The message domain at parameter `l` — what is absorbed after the tag. -/
  D : ℕ → Type
  /-- The digest space at parameter `l`. -/
  R : ℕ → Type
  /-- The key space is finite. -/
  keyFin : ∀ l, Fintype (Key l)
  /-- Decidable equality on keys. -/
  keyDec : ∀ l, DecidableEq (Key l)
  /-- The key space is inhabited (a tag is always available). -/
  keyNe : ∀ l, Nonempty (Key l)
  /-- The domain is finite. -/
  dFin : ∀ l, Fintype (D l)
  /-- Decidable equality on the domain. -/
  dDec : ∀ l, DecidableEq (D l)
  /-- The domain is inhabited. -/
  dNe : ∀ l, Nonempty (D l)
  /-- The range is finite. -/
  rFin : ∀ l, Fintype (R l)
  /-- Decidable equality on the range. -/
  rDec : ∀ l, DecidableEq (R l)
  /-- The range is inhabited. -/
  rNe : ∀ l, Nonempty (R l)

/-- **THE KEYED FAMILY AS A PLAIN RANDOM-ORACLE FAMILY** — the tag folds into the domain. The oracle
is `H : (Key l × D l) → R l`, so a collision is between two DISTINCT tagged messages, which is exactly
domain-separated collision resistance of the sponge that absorbs `tagCode t ++ msg`. -/
def KeyedRomFamily.toRomFamily (F : KeyedRomFamily) : RomFamily where
  D := fun l => F.Key l × F.D l
  R := F.R
  dFin := fun l => by letI := F.keyFin l; letI := F.dFin l; infer_instance
  dDec := fun l => by letI := F.keyDec l; letI := F.dDec l; infer_instance
  dNe := fun l => by letI := F.keyNe l; letI := F.dNe l; exact inferInstance
  rFin := F.rFin
  rDec := F.rDec
  rNe := F.rNe

/-- **THE KEYED COLLISION GAME.** The instance is the sampled keyed oracle; the adversary outputs two
tagged messages and WINS iff they are distinct with equal digest. This is `romCollisionGame` over the
tag-separated domain — the deployed shape of a domain-separated hash's collision game. -/
def keyedRomGame (F : KeyedRomFamily) : Game := romCollisionGame F.toRomFamily

/-- **THE QUERY-BOUNDED KEYED ADVERSARY CLASS — the fixed `Eff`.** `A` factors through a `Q`-query
oracle tree over the tag-separated domain. It is a restriction on the SAME raw adversary type the
floor quantifies over, so it plugs into `FloorGames.Hard` unchanged, and the key/oracle it attacks is
sampled AFTER the tree is fixed. -/
def KeyedRomEff (F : KeyedRomFamily) (Q : ℕ → ℕ) : Adversary (keyedRomGame F) → Prop :=
  RomEff F.toRomFamily Q

/-! ## §2 — THE FLOOR, PROVED (not assumed). -/

/-- **⚑⚑ THE KEYED HASH FLOOR, PROVED.** At a `λ`-growing digest space (`|R l| = 2^l`, the deployed
shape) and a polynomially bounded query budget, EVERY query-bounded keyed adversary's collision
advantage is negligible. Directly `RomQueryFloor.romCollision_hard` at the tag-separated family: the
birthday bound, with NO cryptographic assumption under it. This is what replaces
`HashCRHardQuant (spongeFamily D) (IsPolyTime …)`, whose hypothesis is FALSE. -/
theorem keyedRom_hard (F : KeyedRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l) :
    Hard (keyedRomGame F) (KeyedRomEff F Q) :=
  romCollision_hard F.toRomFamily Q hQ hw

/-! ## §3 — ⚑ THE COUNTEREXAMPLE DIES.

The refutation `sysRoots_floor_polyTime_false_babyBear` builds `shortCollAdv`: an adversary answering
each sampled tag with a fixed two-limb collision that EXISTS in the fixed compressing sponge, hence
wins with probability `1`, hence refutes the `IsPolyTime` floor. This section proves that strategy no
longer refutes the keyed/query-counted floor — in the two complementary ways the fix works. -/

/-- **THE GENERAL EXCLUSION.** A keyed adversary whose advantage is NOT negligible is OUTSIDE
`KeyedRomEff`: if it were inside, `keyedRom_hard` would make its advantage negligible. This is the
form of the death of every `shortCollAdv`-style refuter — the class the floor quantifies over does not
contain the adversary the refutation needs. -/
theorem not_keyedRomEff_of_not_negl (F : KeyedRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (A : Adversary (keyedRomGame F)) (hnn : ¬ Negl (gameAdv (keyedRomGame F) A)) :
    ¬ KeyedRomEff F Q A :=
  fun hmem => hnn (keyedRom_hard F Q hQ hw A hmem)

/-- **⚑ (a) THE FULL-ORACLE `Classical.choice` ANSWERER IS EXCLUDED.** The adversary that reads the
whole sampled oracle and returns a collision wherever one exists — the `shortCollAdv` analogue in the
random oracle model — is NOT in `KeyedRomEff`. It would have to know a collision of an oracle it never
queried; `RomOracle.OracleComp.eval_congr_of_agree_on_queried` forbids that. Directly
`RomQueryFloor.choiceAdv_not_romEff`. -/
theorem keyedChoiceAdv_excluded (F : KeyedRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (hcompress : ∀ l, letI := (F.toRomFamily).dFin l; letI := (F.toRomFamily).rFin l;
      Fintype.card (F.toRomFamily.R l) < Fintype.card (F.toRomFamily.D l))
    (hne : ∀ l, Nonempty ((keyedRomGame F).Ans l)) :
    ¬ KeyedRomEff F Q (choiceAdv (keyedRomGame F) hne) :=
  choiceAdv_not_romEff F.toRomFamily Q hQ hw hcompress hne

/-! ### (b) The FIXED short-collision answerer — the exact `IsPolyTime`-refuting shape — is defanged. -/

/-- **THE FIXED-PAIR ANSWERER** — the random-oracle transplant of `shortCollAdv`: it ignores the
oracle and returns a FIXED pair of distinct tagged messages `(x l, y l)`. As a `0`-query tree it is
admitted by `KeyedRomEff`; that is the whole point of (b) — the class does NOT exclude it, and it does
not need to, because its advantage collapses. -/
def fixedPairComp (F : KeyedRomFamily) (x y : ∀ l, F.toRomFamily.D l) : RomComp F.toRomFamily :=
  fun l => OracleComp.pure (x l, y l)

/-- **THE FIXED-PAIR ANSWERER IS `0`-QUERY, HENCE IN THE CLASS.** So (b) is genuinely the case where
the refuting *shape* is admitted — unlike (a), which is excluded. -/
theorem fixedPairAdv_in_keyedRomEff (F : KeyedRomFamily) (Q : ℕ → ℕ)
    (x y : ∀ l, F.toRomFamily.D l) :
    KeyedRomEff F Q (romAdv F.toRomFamily (fixedPairComp F x y)) :=
  ⟨fixedPairComp F x y, fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩

/-- Its win event at each oracle is exactly "the two fixed points collide under `H`". -/
theorem fixedPairAdv_hit (F : KeyedRomFamily) (l : ℕ) (x y : ∀ l, F.toRomFamily.D l)
    (hxy : x l ≠ y l) (H : (keyedRomGame F).Inst l) :
    letI := (F.toRomFamily).rDec l
    (romAdv F.toRomFamily (fixedPairComp F x y)).hit l H
      = decide (H (x l) = H (y l)) := by
  letI := (F.toRomFamily).dDec l; letI := (F.toRomFamily).rDec l
  rw [romAdv_hit F.toRomFamily (fixedPairComp F x y) l H]
  show collWin (OracleComp.pure (x l, y l)) H = decide (H (x l) = H (y l))
  refine (collWin_pure (x l, y l) H).trans ?_
  simp [hxy]

/-- **⚑ (b) THE FIXED ANSWERER'S ADVANTAGE IS EXACTLY `1/|R|`.** Over the SAMPLED oracle a fixed pair
of distinct points collides with probability exactly `1/|R l|` (`condProb_two_fresh_eq` at the empty
conditioning). Against the *fixed* sponge the same fixed pair collides with probability `1` (the
collision is real); sampling the oracle after the adversary is what turns `1` into `1/|R|`. -/
theorem fixedPairAdv_gameAdv_eq (F : KeyedRomFamily) (l : ℕ) (x y : ∀ l, F.toRomFamily.D l)
    (hxy : x l ≠ y l) :
    gameAdv (keyedRomGame F) (romAdv F.toRomFamily (fixedPairComp F x y)) l
      = 1 / (letI := (F.toRomFamily).rFin l; (Fintype.card (F.toRomFamily.R l) : ℝ)) := by
  letI := (F.toRomFamily).dFin l; letI := (F.toRomFamily).dDec l
  letI := (F.toRomFamily).rFin l; letI := (F.toRomFamily).rDec l; letI := (F.toRomFamily).rNe l
  have hkey := condProb_two_fresh_eq (D := F.toRomFamily.D l) (R := F.toRomFamily.R l) ∅
    (fun _ => Classical.arbitrary (F.toRomFamily.R l)) (x l) (y l) (by simp) (by simp) hxy
  rw [condProb_cyl_empty] at hkey
  simp only [gameAdv, keyedRomGame]
  rw [show ((romAdv F.toRomFamily (fixedPairComp F x y)).hit l)
        = (fun H => decide (H (x l) = H (y l))) from
      funext (fun H => fixedPairAdv_hit F l x y hxy H)]
  exact hkey

/-- **⚑ (b) THE FIXED ANSWERER'S ADVANTAGE IS NEGLIGIBLE.** At a `λ`-bit digest space its advantage is
`1/2^l`, negligible. So the exact adversary shape that refutes `HashCRHardQuant (spongeFamily D)
(IsPolyTime …)` with probability `1` does NOT refute the keyed/query-counted floor — its advantage is
below every inverse polynomial. This is the sharpest statement of the counterexample dying. -/
theorem fixedPairAdv_negl (F : KeyedRomFamily) (x y : ∀ l, F.toRomFamily.D l)
    (hxy : ∀ l, x l ≠ y l)
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l) :
    Negl (gameAdv (keyedRomGame F) (romAdv F.toRomFamily (fixedPairComp F x y))) := by
  have heq : gameAdv (keyedRomGame F) (romAdv F.toRomFamily (fixedPairComp F x y))
      = fun l => 1 / (2 : ℝ) ^ l := by
    funext l
    rw [fixedPairAdv_gameAdv_eq F l x y (hxy l)]
    show 1 / (letI := (F.toRomFamily).rFin l; (Fintype.card (F.toRomFamily.R l) : ℝ)) = _
    have : (letI := (F.toRomFamily).rFin l; Fintype.card (F.toRomFamily.R l)) = 2 ^ l := hw l
    rw [this]
    push_cast
    ring
  rw [heq]
  exact negl_two_pow

/-! ## §4 — BOTH POLES, at the fixed model. -/

/-- **⚑ THE ⊤ POLE — the UNRESTRICTED floor at the keyed game is FALSE.** A collision exists at every
oracle of a compressing family (pigeonhole), so `solvableFrac = 1` and the unrestricted floor is
refuted. Same game, same win relation — the query bound is doing real work. -/
theorem keyedRom_top_false (F : KeyedRomFamily)
    (hc : ∀ l, letI := (F.toRomFamily).dFin l; letI := (F.toRomFamily).rFin l;
      Fintype.card (F.toRomFamily.R l) < Fintype.card (F.toRomFamily.D l)) :
    ¬ Hard (keyedRomGame F) (fun _ => True) :=
  romCollision_top_false F.toRomFamily hc

/-- **⚑ THE ⊥ POLE — the class contains a REAL two-query adversary with POSITIVE advantage.** It
queries two tagged points and outputs them iff they collide, winning with advantage exactly `1/|R l|
> 0`. So `KeyedRomEff` is not the empty class in disguise, and `keyedRom_hard` is a statement about
something. -/
theorem twoPointKeyed_in_keyedRomEff (F : KeyedRomFamily) (Q : ℕ → ℕ) (hQ : ∀ l, 2 ≤ Q l)
    (x y : ∀ l, F.toRomFamily.D l) :
    KeyedRomEff F Q (romAdv F.toRomFamily (fun l => twoPointComp F.toRomFamily l (x l) (y l))) :=
  twoPointAdv_in_romEff F.toRomFamily Q hQ x y

/-- The two-query keyed adversary's advantage is positive at every parameter. -/
theorem twoPointKeyed_gameAdv_pos (F : KeyedRomFamily) (l : ℕ) (x y : ∀ l, F.toRomFamily.D l)
    (hxy : x l ≠ y l) :
    0 < gameAdv (keyedRomGame F) (romAdv F.toRomFamily
      (fun l => twoPointComp F.toRomFamily l (x l) (y l))) l :=
  twoPointAdv_gameAdv_pos F.toRomFamily l x y hxy

/-! ## §5 — a DEPLOYED-SHAPE keyed instance, and the whole verdict at one family.

A `λ`-bit digest, a strictly larger tag-separated domain (four tags, `2·2^l` messages each), i.e.
compressing — the shape a domain-separated sponge has. Everything above fires on it. -/

/-- **THE DEPLOYED-SHAPE KEYED FAMILY.** Four tags, `2·2^l` messages, a `2^l`-element digest space —
`|Key × D| = 8·2^l > 2^l = |R|`, compressing. -/
def deployedKeyedFamily : KeyedRomFamily where
  Key := fun _ => Fin 4
  D := fun l => Fin (2 * 2 ^ l)
  R := fun l => Fin (2 ^ l)
  keyFin := fun _ => inferInstance
  keyDec := fun _ => inferInstance
  keyNe := fun _ => ⟨0⟩
  dFin := fun _ => inferInstance
  dDec := fun _ => inferInstance
  dNe := fun l => ⟨⟨0, by positivity⟩⟩
  rFin := fun _ => inferInstance
  rDec := fun _ => inferInstance
  rNe := fun l => ⟨⟨0, by positivity⟩⟩

theorem deployedKeyed_card_R (l : ℕ) :
    letI := deployedKeyedFamily.rFin l
    Fintype.card (deployedKeyedFamily.R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

theorem deployedKeyed_compressing (l : ℕ) :
    letI := (deployedKeyedFamily.toRomFamily).dFin l; letI := (deployedKeyedFamily.toRomFamily).rFin l
    Fintype.card (deployedKeyedFamily.toRomFamily.R l)
      < Fintype.card (deployedKeyedFamily.toRomFamily.D l) := by
  show Fintype.card (Fin (2 ^ l)) < Fintype.card (Fin 4 × Fin (2 * 2 ^ l))
  simp only [Fintype.card_prod, Fintype.card_fin]
  have : 0 < 2 ^ l := by positivity
  nlinarith

/-- **(TOOTH — the unrestricted floor is FALSE at the deployed shape.)** -/
theorem deployedKeyed_top_false :
    ¬ Hard (keyedRomGame deployedKeyedFamily) (fun _ => True) :=
  keyedRom_top_false deployedKeyedFamily deployedKeyed_compressing

/-- **⚑⚑⚑ THE WHOLE VERDICT AT ONE CONCRETE KEYED FAMILY AND ONE CONCRETE BUDGET.**

At `Q l = l + 2` on the deployed-shape keyed family, all four facts at once:

  1. the keyed/query-counted floor is **TRUE** (`keyedRom_hard`);
  2. the class is **INHABITED** by an adversary that really queries and really wins (positive
     advantage);
  3. the unrestricted floor **at the same game** is **FALSE** — so the query bound is load-bearing;
  4. **THE COUNTEREXAMPLE DIES BOTH WAYS**: the fixed short-collision answerer (the `IsPolyTime`
     refuter's shape) is admitted but its advantage is negligible.

So the floor is not vacuous, the class is neither `⊤` nor `⊥`, and the `shortCollAdv`-style refutation
that kills the `IsPolyTime` floor cannot touch this one. -/
theorem deployedKeyed_verdict :
    Hard (keyedRomGame deployedKeyedFamily) (KeyedRomEff deployedKeyedFamily (fun l => l + 2))
      ∧ (∃ A, KeyedRomEff deployedKeyedFamily (fun l => l + 2) A
              ∧ ∀ l, 0 < gameAdv (keyedRomGame deployedKeyedFamily) A l)
      ∧ ¬ Hard (keyedRomGame deployedKeyedFamily) (fun _ => True)
      ∧ (∃ A, KeyedRomEff deployedKeyedFamily (fun l => l + 2) A
              ∧ Negl (gameAdv (keyedRomGame deployedKeyedFamily) A)) := by
  have hlt : ∀ l : ℕ, 1 < 2 * 2 ^ l := by
    intro l
    have : 0 < 2 ^ l := by positivity
    omega
  let x : ∀ l, deployedKeyedFamily.toRomFamily.D l :=
    fun l => ((0 : Fin 4), (⟨0, by have := hlt l; omega⟩ : Fin (2 * 2 ^ l)))
  let y : ∀ l, deployedKeyedFamily.toRomFamily.D l :=
    fun l => ((0 : Fin 4), (⟨1, hlt l⟩ : Fin (2 * 2 ^ l)))
  have hxy : ∀ l, x l ≠ y l := by
    intro l h
    have h2 : (0 : ℕ) = 1 := congrArg (fun p => (p.2 : Fin (2 * 2 ^ l)).val) h
    exact absurd h2 (by norm_num)
  refine ⟨keyedRom_hard deployedKeyedFamily (fun l => l + 2) ⟨2, 6, ?_⟩ deployedKeyed_card_R,
    ⟨romAdv deployedKeyedFamily.toRomFamily
        (fun l => twoPointComp deployedKeyedFamily.toRomFamily l (x l) (y l)),
      twoPointKeyed_in_keyedRomEff deployedKeyedFamily (fun l => l + 2)
        (fun l => Nat.le_add_left 2 l) x y,
      fun l => twoPointKeyed_gameAdv_pos deployedKeyedFamily l x y (hxy l)⟩,
    deployedKeyed_top_false,
    ⟨romAdv deployedKeyedFamily.toRomFamily (fixedPairComp deployedKeyedFamily x y),
      fixedPairAdv_in_keyedRomEff deployedKeyedFamily (fun l => l + 2) x y,
      fixedPairAdv_negl deployedKeyedFamily x y hxy deployedKeyed_card_R⟩⟩
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  keyedRom_hard,
  not_keyedRomEff_of_not_negl,
  keyedChoiceAdv_excluded,
  fixedPairAdv_in_keyedRomEff,
  fixedPairAdv_hit,
  fixedPairAdv_gameAdv_eq,
  fixedPairAdv_negl,
  keyedRom_top_false,
  twoPointKeyed_in_keyedRomEff,
  twoPointKeyed_gameAdv_pos,
  deployedKeyed_card_R,
  deployedKeyed_compressing,
  deployedKeyed_top_false,
  deployedKeyed_verdict
]

end Dregg2.Crypto.KeyedRomFloor
