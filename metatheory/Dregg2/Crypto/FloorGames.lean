/-
# `Dregg2.Crypto.FloorGames` — the `*HardQuant` floors RESTATED as the standard cryptographic games,
with the problem IN the statement, and the DILEMMA localized to its one real cause.

## What was wrong (proved in `HardQuantVacuity`, 2026-07-16)

The five `*HardQuant` floors were **one `Prop`**:

    def MSISHardQuant {S : Type*} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)

`Iff.rfl` five ways. None mentioned a lattice, a curve, a hash or `IsMSISSolution`; the problem lived
entirely in the NAME. `HardQuantVacuity.the_vrf_keystone_accepts_the_hash_floor` passed a
`HashCRHardQuant` proof into the slot `VrfRegrounded.lattice_vrf_uniqueness_advantage_bound` declares as
`MSISHardQuant` and it TYPECHECKED. The old shape survives, doc-marked, as
`ProbCrypto.MSISHardQuantShape` and friends — the record matters, and those teeth are the regression.

## What this file does

**§1 — ONE SCHEMA, MANY PROBLEMS.** A `Game` is a λ-indexed finite `Inst`ance space, an `Ans`wer space,
and a **win relation** `wins l i a`. An `Adversary` is `run : ∀ l, Inst l → Ans l`; its `gameAdv` is the
`winProb` — the fraction of instances at parameter `l` on which it wins. This is the tree's existing
`ProbCrypto.winProb`/`ConcreteSecurity.Negl` machinery; nothing probabilistic is invented.

    def Hard (G : Game) (Eff : Adversary G → Prop) : Prop := ∀ A, Eff A → Negl (gameAdv G A)

The five floors are this schema at **five different `Game`s**, each carrying its problem: `IsMSISSolution`
(§3), the MLWE secret (§4), a discrete log (§5), a hash collision (§6, reusing
`HashFloorHonesty.KeyedHashFamily`), and the LWE-vs-uniform distinguishing gap (§7). The old defect —
five names, one `Prop` — is gone at the TYPE level: `MSISHardQuant F Eff` and `HashCRHardQuant H Eff'`
are `Hard` at incomparable `Game`s, so the wrong-floor proof no longer elaborates
(`HardQuantVacuity` §6 is the permanent tooth).

**§2 — THE COLLAPSE, and it decides the dilemma.** `hard_top_iff_solvableFrac_negl`:

    Hard G (fun _ => True)  ↔  Negl (solvableFrac G)

At the **unrestricted** adversary class, a game floor IS the (probabilistic) EXISTENCE floor — the
`Classical.choice` adversary that picks a winning answer wherever one exists wins on exactly the solvable
instances. So the sweep's Horn A is **not an artifact of `msisSolverAdv`, and not an artifact of the old
shape**: it is a theorem about EVERY unrestricted-adversary formulation, this one included. At a
compressing MSIS instance solutions exist at every coin, so `MSISHardQuant F ⊤` is FALSE
(`msisHardQuant_top_false_of_compressing`), exactly as `Lattice.MSISHard` is.

⚑ **This refutes the repair the sweep itself named.** `HashFloorHonesty.CollisionResistant F` WAS
`HashCRHardQuant F ⊤` under another name, and `hashCRHardQuant_top_false_of_compressing` proves the
"proper keyed computational floor" — the pattern
`VACUITY-SWEEP.md` §Finding-1 prescribes as *"the correct pattern already in the tree"* — is itself FALSE
at deployed parameters, for the same pigeonhole reason, laundered through `Classical.choice`. A keyed
family does not fix it. Copying that pattern to the lattice floors would have been the FOURTH costume.

**§8 — WHAT ACTUALLY ESCAPES, and the residual, named.** The quantifier `∀ A : Adversary G` ranges over
every Lean function, and a function may pick a solution it could never compute. Hardness quantifies over
**EFFICIENT** adversaries; the escape is therefore the `Eff` parameter, and NOTHING ELSE escapes
(`hard_top_iff_solvableFrac_negl` is an `↔`: no restatement of the win relation can help). What the
repair buys is exact and it is not nothing:

  1. the problem is IN the statement (`msisSolver_wins_iff` etc. unfold `wins` to `IsMSISSolution`),
  2. the floors are pairwise non-interchangeable (five `Game`s, not one `Prop`),
  3. consumers must EXHIBIT a reduction (`VrfRegrounded.vrf_uniqueness_adversary_is_msis_solver`
     constructs the solver and PROVES the advantage inequality — the reduction is in the proof, not the
     docstring),
  4. the dilemma is localized to ONE named object, `Eff`, with both poles PROVED here: `Eff := ⊤` makes
     every floor FALSE at deployed parameters (`hard_top_iff_solvableFrac_negl`), `Eff := ⊥` makes it
     vacuous (`hard_bot_vacuous`).

⚑ **THE RESIDUAL, stated precisely and NOT closed here: the tree has no cost model.** `Eff` cannot be
given honest content by anything in this repository — `Computable` does not restrict it (every instance is
a finite object, so brute-force search is computable: `computable_does_not_restrict`), and Mathlib has no
polynomial-time model over an arbitrary carrier. So `Eff` is carried as a PARAMETER, and every consumer
that discharges a floor leaf carries an `Eff`-membership obligation for the solver its reduction builds.
That obligation is the honest name for "the reduction is efficient". It is undischarged, it is labelled
at every use site, and it is the whole remaining gap between this floor and a cryptographic assumption.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no `def …Hard`
used as a hypothesis. Every verdict is PROVED. `Classical.choice` is not incidental here — it is the
adversary in §2, and it is why §8's residual is real.
-/
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.Lattice
import Dregg2.Crypto.ProbCrypto
import Dregg2.Crypto.SchnorrCurveField
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.FloorGames

open Dregg2.Crypto.ConcreteSecurity
  (Ensemble Negl negl_zero not_negl_one negl_two_pow negl_of_eventually_le negl_finset_sum)
open Dregg2.Crypto.ProbCrypto (winProb winProb_nonneg winProb_le_one winProb_top winProb_bot)
open Dregg2.Crypto.Lattice (ShortNorm IsMSISSolution IsMLWESample nrm)

set_option autoImplicit false

/-! ## §1 — the schema: a λ-indexed security GAME, its adversaries, and their advantage.

Nothing here is new machinery: `winProb` is `ProbCrypto`'s finite counting probability and `Negl` is
`ConcreteSecurity`'s. What is new — and what the old floors lacked — is that a `Game` CARRIES its win
relation, so a floor stated over it mentions its problem. -/

/-- **A λ-indexed security game.** At each security parameter `l`: a FINITE, inhabited instance space
`Inst l` (the challenge, sampled uniformly — for MSIS the public matrix, for hash-CR the key, for DL the
challenge point), an answer space `Ans l` (the solution the adversary outputs), and the **win relation**
`wins l i a` — the actual problem. `winsDec` makes the win event a genuine finite counting event.

The instance space is what makes the floor λ-indexed and therefore non-degenerate: a single-instance
"∃ efficient adversary" collapses to "∃ solution" by non-uniform hardcoding, which is exactly the trap
`CryptoFloorTeeth` §5 documents. -/
structure Game where
  /-- The instance (challenge) space at parameter `l`, sampled uniformly. -/
  Inst : ℕ → Type
  /-- The answer space at parameter `l` — what the adversary outputs. -/
  Ans : ℕ → Type
  /-- The instance space is finite (the game samples a uniform instance). -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited (a non-empty outcome space). -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- **THE PROBLEM.** `wins l i a` holds iff `a` is a genuine solution to instance `i` at parameter `l`.
  This field is the whole difference between this floor and its content-free predecessor. -/
  wins : ∀ l, Inst l → Ans l → Prop
  /-- The win event is decidable — it is counted, so it must be. -/
  winsDec : ∀ l (i : Inst l) (a : Ans l), Decidable (wins l i a)

/-- **An adversary against `G`.** It receives the instance and outputs an answer. NOTE what this type does
NOT say: nothing bounds its resources. `Adversary G` is every Lean function `∀ l, G.Inst l → G.Ans l`,
including ones that pick an answer by `Classical.choice` — which is precisely why §2's collapse holds and
why the `Eff` parameter of `Hard` is not decoration. -/
structure Adversary (G : Game) where
  /-- The adversary's output on instance `i` at parameter `l`. -/
  run : ∀ l, G.Inst l → G.Ans l

/-- The adversary **wins** on instance `i` iff its answer genuinely solves `i` — `G.wins` at its own
output. Decided by the game's own `winsDec`. -/
def Adversary.hit {G : Game} (A : Adversary G) (l : ℕ) (i : G.Inst l) : Bool :=
  @decide _ (G.winsDec l i (A.run l i))

/-- The win event, as a proposition: the adversary hits iff its answer solves the instance. The Bool/Prop
bridge every counting argument below goes through. -/
theorem Adversary.hit_eq_true {G : Game} (A : Adversary G) (l : ℕ) (i : G.Inst l) :
    A.hit l i = true ↔ G.wins l i (A.run l i) := by
  unfold Adversary.hit
  simp only [decide_eq_true_eq]

/-- **The adversary's advantage ensemble**: at parameter `l`, the fraction of instances it solves — a
genuine real in `[0,1]` (`gameAdv_mem_unit`), the concrete-security object. -/
noncomputable def gameAdv (G : Game) (A : Adversary G) : Ensemble :=
  fun l => @winProb (G.Inst l) (G.instFin l) (A.hit l)

theorem gameAdv_mem_unit (G : Game) (A : Adversary G) (l : ℕ) :
    0 ≤ gameAdv G A l ∧ gameAdv G A l ≤ 1 :=
  ⟨@winProb_nonneg _ (G.instFin l) _, @winProb_le_one _ (G.instFin l) _⟩

/-- **THE FLOOR SCHEMA.** Every adversary IN THE CLASS `Eff` has negligible advantage at the game `G`.

Two parameters, and both are load-bearing:

  * `G` carries the PROBLEM. `Hard G₁ Eff` and `Hard G₂ Eff'` are different `Prop`s for different games —
    this is what makes the five floors non-interchangeable, and it is what the old shape lacked.
  * `Eff` carries the RESOURCE BOUND — "efficient". It is a PARAMETER because this repository has no cost
    model (§8). At `Eff := ⊤` the floor is the existence floor and is FALSE at deployed parameters (§2);
    at `Eff := ⊥` it is vacuous (`hard_bot_vacuous`). A floor is exactly as honest as its `Eff`, and no
    restatement of `wins` can substitute for one. -/
def Hard (G : Game) (Eff : Adversary G → Prop) : Prop :=
  ∀ A : Adversary G, Eff A → Negl (gameAdv G A)

/-! ## §2 — THE COLLAPSE: at the unrestricted class, a game floor IS the existence floor.

This is the load-bearing theorem of the file. The sweep proved Horn A of its dilemma for ONE `adv`
(`FloorBridge.msisSolverAdv`) and concluded "no third instantiation exists **in the current shape**". The
`↔` below says more, and it says it about the REPAIRED shape: for ANY game whatsoever, quantifying over
all adversaries makes the floor equivalent to "the solvable fraction is negligible". Restating the win
relation cannot escape the dilemma. Only `Eff` can. -/

/-- **An instance is SOLVABLE** iff some answer wins on it — the event `∃ solution`, as a counted Bool.
(`Classical.propDecidable` supplies the instance; whether a solution exists is not in general decidable,
and that is exactly the point of the game form.) -/
noncomputable def solvable (G : Game) (l : ℕ) (i : G.Inst l) : Bool :=
  @decide (∃ a, G.wins l i a) (Classical.propDecidable _)

theorem solvable_eq_true (G : Game) (l : ℕ) (i : G.Inst l) :
    solvable G l i = true ↔ ∃ a, G.wins l i a := by
  unfold solvable
  simp only [decide_eq_true_eq]

/-- **The solvable fraction**: at parameter `l`, the fraction of instances that HAVE a winning answer —
the probabilistic form of `∃ solution`. -/
noncomputable def solvableFrac (G : Game) : Ensemble :=
  fun l => @winProb (G.Inst l) (G.instFin l) (solvable G l)

/-- **THE CHOICE ADVERSARY** — it answers each instance with a winning answer wherever one exists. It is a
perfectly good `Adversary G`: nothing in that type demands computability, let alone efficiency. This is
the adversary that collapses every unrestricted floor. -/
noncomputable def choiceAdv (G : Game) (hne : ∀ l, Nonempty (G.Ans l)) : Adversary G where
  run := fun l i =>
    letI := Classical.propDecidable (∃ a, G.wins l i a)
    if h : ∃ a, G.wins l i a then h.choose else (hne l).some

/-- The choice adversary wins on exactly the solvable instances. -/
theorem choiceAdv_hit (G : Game) (hne : ∀ l, Nonempty (G.Ans l)) (l : ℕ) (i : G.Inst l) :
    (choiceAdv G hne).hit l i = solvable G l i := by
  rw [Bool.eq_iff_iff, Adversary.hit_eq_true, solvable_eq_true]
  refine ⟨fun hw => ⟨_, hw⟩, fun h => ?_⟩
  simp only [choiceAdv, dif_pos h]
  exact h.choose_spec

/-- The choice adversary's advantage IS the solvable fraction. -/
theorem choiceAdv_gameAdv (G : Game) (hne : ∀ l, Nonempty (G.Ans l)) :
    gameAdv G (choiceAdv G hne) = solvableFrac G := by
  funext l
  unfold gameAdv solvableFrac
  congr 1
  funext i
  exact choiceAdv_hit G hne l i

/-- Any adversary's advantage is at most the solvable fraction — it can only win where a win exists. -/
theorem gameAdv_le_solvableFrac (G : Game) (A : Adversary G) (l : ℕ) :
    gameAdv G A l ≤ solvableFrac G l := by
  unfold gameAdv solvableFrac
  refine @Dregg2.Crypto.ProbCrypto.winProb_le_of_imp _ (G.instFin l) _ _ (fun i hi => ?_)
  rw [solvable_eq_true]
  exact ⟨A.run l i, (A.hit_eq_true l i).mp hi⟩

/-- **⚑ THE COLLAPSE — a floor over ALL adversaries IS the probabilistic existence floor.**

    Hard G (fun _ => True)  ↔  Negl (solvableFrac G)

Left-to-right is the `choiceAdv`: it is an adversary, so the floor bounds it, and its advantage is the
solvable fraction. Right-to-left is domination: no adversary wins where nothing wins.

**This is the dilemma, generalized and PROVED for the repaired shape.** The sweep's Horn A blamed a
particular `adv` (`FloorBridge.msisSolverAdv`, the solution-indexed family) and its conclusion — "the only
MSIS-tied `adv` collapses to the Boolean floor" — reads like an accident of that instantiation. It is not.
Tie the advantage to the problem in ANY way at all, quantify over all adversaries, and you get the
existence floor back. `Classical.choice` is the adversary; the win relation cannot see it coming. The one
hypothesis that is doing work here is `hne` (some answer exists to fall back on), and it is satisfied by
every real game.

So: **the escape is not in the shape of `wins`. It is `Eff`, and only `Eff`** — the standard form's
"for every EFFICIENT adversary". Which this repository cannot state (§8). -/
theorem hard_top_iff_solvableFrac_negl (G : Game) (hne : ∀ l, Nonempty (G.Ans l)) :
    Hard G (fun _ => True) ↔ Negl (solvableFrac G) := by
  constructor
  · intro hhard
    have h := hhard (choiceAdv G hne) trivial
    rwa [choiceAdv_gameAdv] at h
  · intro hsolv A _
    refine negl_of_eventually_le (Filter.Eventually.of_forall (fun l => ?_)) hsolv
    have h0 : 0 ≤ gameAdv G A l := (gameAdv_mem_unit G A l).1
    have h1 : gameAdv G A l ≤ solvableFrac G l := gameAdv_le_solvableFrac G A l
    rw [abs_of_nonneg h0, abs_of_nonneg (le_trans h0 h1)]
    exact h1

/-- **(THE OTHER POLE — the empty class is vacuous.)** At `Eff := ⊥` no adversary is quantified over, so
the floor holds for ANY game, including a completely broken one. Stated so that the `Eff` parameter cannot
be quietly filled with nothing: an `Eff` is exactly as good as its content, and both degenerate choices
are refuted here. -/
theorem hard_bot_vacuous (G : Game) : Hard G (fun _ => False) :=
  fun _ h => absurd h not_false

/-- **A game whose instances are all solvable has NO unrestricted floor.** The specialization of the
collapse that every "false at deployed parameters" tooth below routes through: if a winning answer exists
at every instance, the solvable fraction is the constant `1`, which is not negligible. Compressing
hashes and compressing lattice maps are exactly this situation — by pigeonhole. -/
theorem not_hard_top_of_always_solvable (G : Game) (hne : ∀ l, Nonempty (G.Ans l))
    (hsolv : ∀ l (i : G.Inst l), ∃ a, G.wins l i a) : ¬ Hard G (fun _ => True) := by
  intro hhard
  have h := (hard_top_iff_solvableFrac_negl G hne).mp hhard
  have hone : solvableFrac G = fun _ => (1 : ℝ) := by
    funext l
    unfold solvableFrac
    have hall : solvable G l = (fun _ => true) := by
      funext i; rw [Bool.eq_iff_iff, solvable_eq_true]; exact ⟨fun _ => rfl, fun _ => hsolv l i⟩
    rw [hall]
    exact @winProb_top _ (G.instFin l) (G.instNe l)
  rw [hone] at h
  exact not_negl_one h

/-- **THE POSITIVE TWIN — a game whose instances are NEVER solvable HAS the unrestricted floor.** If no
answer wins at any instance the solvable fraction is `0`, so even the choice adversary gets nothing.

⚑ Read it with its twin above and the range is the whole story: the `⊤` floor holds exactly when
nothing can be found, and fails as soon as something can. That is why a `⊤`-class floor is never a
security assumption — it is a restatement of "no solution exists" — and why every SATISFIABILITY
witness for a `⊤` floor in this tree is an injective (i.e. non-compressing, i.e. not-a-hash) family.
Added 2026-07-28 to carry the satisfiability poles that `HashFloorHonesty.injective_family_CR` and
`.idFamily_CR` used to carry against the deleted `CollisionResistant`. No `hne` is needed here — the
twin needs it only to build the choice adversary, and an unsolvable game needs no adversary built. -/
theorem hard_top_of_never_solvable (G : Game)
    (hns : ∀ l (i : G.Inst l) (a : G.Ans l), ¬ G.wins l i a) : Hard G (fun _ => True) := by
  intro A _
  have hzero : gameAdv G A = fun _ => (0 : ℝ) := by
    funext l
    show @winProb (G.Inst l) (G.instFin l) (A.hit l) = 0
    have hall : A.hit l = (fun _ => false) := by
      funext i
      rw [Bool.eq_false_iff, ne_eq, Adversary.hit_eq_true]
      exact hns l i (A.run l i)
    rw [hall]
    exact @winProb_bot _ (G.instFin l)
  rw [hzero]
  exact negl_zero

/-! ## §3 — MSIS: the search floor, with `IsMSISSolution` IN the statement. -/

/-- **An MSIS instance FAMILY.** At each security parameter `l` a module pair `M l`, `N l` over `Rq l`
with a shortness seminorm, a FINITE space `Inst l` of public maps sampled uniformly (the instance
randomness — a real MSIS challenge is a uniformly sampled matrix `A`), and the shortness bound `β l`.

The λ-indexing is the growth the floor needs to be asymptotic; the instance sampling is what makes the
advantage a genuine fraction rather than a Boolean flag. -/
structure MSISFamily where
  /-- The base ring `R_q = ℤ_q[X]/(Xⁿ+1)` at parameter `l`. -/
  Rq : ℕ → Type
  /-- The domain module `R_q^m` at parameter `l`. -/
  M : ℕ → Type
  /-- The codomain module `R_q^k` at parameter `l`. -/
  N : ℕ → Type
  /-- `Rq l` is a commutative ring. -/
  rqRing : ∀ l, CommRing (Rq l)
  /-- `M l` is an abelian group. -/
  mGrp : ∀ l, AddCommGroup (M l)
  /-- `M l` is an `Rq l`-module. -/
  mMod : ∀ l, letI := rqRing l; letI := mGrp l; Module (Rq l) (M l)
  /-- The shortness seminorm on `M l` — the lattice-specific ingredient. -/
  mNrm : ∀ l, letI := mGrp l; ShortNorm (M l)
  /-- `N l` is an abelian group. -/
  nGrp : ∀ l, AddCommGroup (N l)
  /-- `N l` is an `Rq l`-module. -/
  nMod : ∀ l, letI := rqRing l; letI := nGrp l; Module (Rq l) (N l)
  /-- Decidable equality on `M l` (the win event checks `z ≠ 0`). -/
  mDec : ∀ l, DecidableEq (M l)
  /-- Decidable equality on `N l` (the win event checks `A z = 0`). -/
  nDec : ∀ l, DecidableEq (N l)
  /-- The instance space: the randomness of the sampled public map. -/
  Inst : ℕ → Type
  /-- The instance space is finite (uniform sampling). -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited. -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The sampled public map `A` at parameter `l` on instance randomness `i`. -/
  A : ∀ l, Inst l →
    (letI := rqRing l; letI := mGrp l; letI := mMod l; letI := nGrp l; letI := nMod l;
     M l →ₗ[Rq l] N l)
  /-- The shortness bound `β` at parameter `l`. -/
  β : ℕ → ℕ

/-- **THE MSIS GAME.** The adversary receives the sampled public map and outputs a candidate vector; it
WINS iff that vector is a genuine `IsMSISSolution` — short, nonzero, in the kernel. `IsMSISSolution` is
`Lattice`'s, unmodified: the problem is IN the game, not in a docstring. -/
def msisGame (F : MSISFamily) : Game where
  Inst := F.Inst
  Ans := F.M
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i z =>
    letI := F.rqRing l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
    letI := F.nGrp l; letI := F.nMod l
    IsMSISSolution (F.A l i) (F.β l) z
  winsDec := fun l i z => by
    letI := F.rqRing l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
    letI := F.nGrp l; letI := F.nMod l; letI := F.mDec l; letI := F.nDec l
    unfold IsMSISSolution
    infer_instance

/-- **⚑ THE PROBLEM IS IN THE STATEMENT.** The MSIS game's win relation UNFOLDS to `IsMSISSolution` — by
`Iff.rfl`, because it IS that predicate. Contrast the old floor, of which no such lemma could be stated:
there was nothing to unfold to. This is the lemma that makes the reduction in
`VrfRegrounded.vrf_uniqueness_adversary_is_msis_solver` transport lattice content. -/
theorem msisGame_wins_iff (F : MSISFamily) (l : ℕ) (i : F.Inst l) (z : F.M l) :
    (msisGame F).wins l i z ↔
      (letI := F.rqRing l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
       letI := F.nGrp l; letI := F.nMod l
       IsMSISSolution (F.A l i) (F.β l) z) :=
  Iff.rfl

/-- **`MSISHardQuant F Eff` — THE MSIS FLOOR, RESTATED.** Every adversary in the class `Eff`, given a
uniformly sampled public map at parameter `l`, finds a short nonzero kernel vector (`IsMSISSolution`) only
with negligible probability. This is the standard Module-SIS game.

Compare what it replaces — `MSISHardQuant {S} (adv : S → Ensemble) := ∀ s, Negl (adv s)` — which mentioned
no lattice and was `Iff.rfl`-equal to the hash floor. The name now has something under it.

⚑ Its honesty is exactly `Eff`'s: at `Eff := ⊤` it is FALSE at compressing parameters
(`msisHardQuant_top_false_of_compressing`), at `Eff := ⊥` vacuous (`hard_bot_vacuous`). §8. -/
def MSISHardQuant (F : MSISFamily) (Eff : Adversary (msisGame F) → Prop) : Prop :=
  Hard (msisGame F) Eff

/-- **THE MSIS FLOOR IS FALSE AT COMPRESSING PARAMETERS — at the unrestricted class.** If at every
parameter and every sampled map the short ball outnumbers the codomain, then a solution EXISTS at every
instance (pigeonhole, exactly `CryptoFloorTeeth.not_msisHard_of_short_ball`'s counting core), so the
solvable fraction is `1` and the collapse (§2) refutes the floor.

This is the deployed situation: a real MSIS matrix is compressing — that is WHY the problem is a hard
SEARCH problem. The floor is therefore not merely unproven at `Eff := ⊤`; it is FALSE there, and every
consumer of it is vacuous. Which is the whole content of §8's residual. -/
theorem msisHardQuant_top_false_of_compressing (F : MSISFamily)
    (hsolv : ∀ l (i : F.Inst l),
      ∃ z, (letI := F.rqRing l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
            letI := F.nGrp l; letI := F.nMod l
            IsMSISSolution (F.A l i) (F.β l) z)) :
    ¬ MSISHardQuant F (fun _ => True) := by
  refine not_hard_top_of_always_solvable (msisGame F) (fun l => ?_) hsolv
  show Nonempty (F.M l)
  letI := F.mGrp l
  exact ⟨0⟩

/-! ## §4 — MLWE (search): the secret IS the win condition.

`Lattice.MLWESearchHard A β t := ¬ ∃ s, short s ∧ ∃ e, short e ∧ t = A s + e` is FALSE at every genuine
public key — the short `(s, e)` ARE the secret key (`CryptoFloorTeeth.not_mlweSearchHard_of_sample`). The
game form does not have that problem *as a statement*: it asks the adversary to RECOVER `s`, which is a
different thing from `s` existing. (It has §2's problem instead, like every game here.) -/

/-- **An MLWE instance family.** At each parameter, a module pair and a public map, plus — per instance
randomness — an actual short secret `s`, an actual short error `e`, and the public sample `t = A·s + e`.
`hsample` PROVES the instance is a genuine MLWE sample (`Lattice.IsMLWESample`), so the family cannot be
filled with something that merely looks like one. -/
structure MLWEFamily where
  /-- The base ring at parameter `l`. -/
  Rq : ℕ → Type
  /-- The secret module at parameter `l`. -/
  M : ℕ → Type
  /-- The sample module at parameter `l`. -/
  N : ℕ → Type
  /-- `Rq l` is a commutative ring. -/
  rqRing : ∀ l, CommRing (Rq l)
  /-- `M l` is an abelian group. -/
  mGrp : ∀ l, AddCommGroup (M l)
  /-- `M l` is an `Rq l`-module. -/
  mMod : ∀ l, letI := rqRing l; letI := mGrp l; Module (Rq l) (M l)
  /-- The shortness seminorm on the secret module. -/
  mNrm : ∀ l, letI := mGrp l; ShortNorm (M l)
  /-- `N l` is an abelian group. -/
  nGrp : ∀ l, AddCommGroup (N l)
  /-- `N l` is an `Rq l`-module. -/
  nMod : ∀ l, letI := rqRing l; letI := nGrp l; Module (Rq l) (N l)
  /-- The shortness seminorm on the sample module (the error's norm). -/
  nNrm : ∀ l, letI := nGrp l; ShortNorm (N l)
  /-- Decidable equality on secrets (the win event checks recovery). -/
  mDec : ∀ l, DecidableEq (M l)
  /-- The instance space (keygen randomness). -/
  Inst : ℕ → Type
  /-- The instance space is finite. -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited. -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The public map at parameter `l`. -/
  A : ∀ l, letI := rqRing l; letI := mGrp l; letI := mMod l; letI := nGrp l; letI := nMod l;
    M l →ₗ[Rq l] N l
  /-- The shortness bound. -/
  β : ℕ → ℕ
  /-- The actual secret at parameter `l` on keygen randomness `i`. -/
  secret : ∀ l, Inst l → M l
  /-- The actual error at parameter `l` on keygen randomness `i`. -/
  err : ∀ l, Inst l → N l
  /-- The secret is short. -/
  secretShort : ∀ l (i : Inst l), letI := mGrp l; letI := mNrm l; nrm (secret l i) ≤ β l
  /-- The error is short. -/
  errShort : ∀ l (i : Inst l), letI := nGrp l; letI := nNrm l; nrm (err l i) ≤ β l

/-- The public sample `t = A·s + e` at parameter `l` on keygen randomness `i`. -/
def MLWEFamily.pub (F : MLWEFamily) (l : ℕ) (i : F.Inst l) : F.N l :=
  letI := F.rqRing l; letI := F.mGrp l; letI := F.mMod l; letI := F.nGrp l; letI := F.nMod l
  F.A l (F.secret l i) + F.err l i

/-- **THE FAMILY IS GENUINELY MLWE.** Every instance's public value IS an `IsMLWESample` — the tree's own
predicate, on the tree's own definition. The family cannot be filled with a non-sample; this is the field
`ProbCrypto.DecisionFamily` lacked, whose absence let its "real world" be anything at all. -/
theorem mlweFamily_isSample (F : MLWEFamily) (l : ℕ) (i : F.Inst l) :
    letI := F.rqRing l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
    letI := F.nGrp l; letI := F.nMod l; letI := F.nNrm l
    IsMLWESample (F.A l) (F.β l) (F.pub l i) :=
  ⟨F.secret l i, F.err l i, F.secretShort l i, F.errShort l i, rfl⟩

/-- **THE MLWE SEARCH GAME.** The adversary receives the keygen randomness' public sample and WINS iff it
outputs the actual secret. Key recovery — the thing MLWE hardness is about — not the existence of a
secret, which is never in doubt. -/
def mlweGame (F : MLWEFamily) : Game where
  Inst := F.Inst
  Ans := F.M
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i s => s = F.secret l i
  winsDec := fun l i s => F.mDec l s (F.secret l i)

/-- **`MLWEHardQuant F Eff` — THE MLWE SEARCH FLOOR, RESTATED.** Every `Eff`-adversary recovers the secret
of a genuine MLWE sample only with negligible probability. -/
def MLWEHardQuant (F : MLWEFamily) (Eff : Adversary (mlweGame F) → Prop) : Prop :=
  Hard (mlweGame F) Eff

/-- **THE MLWE FLOOR IS FALSE AT THE UNRESTRICTED CLASS — always, at every family.** The secret EXISTS at
every instance (it is a field of the family), so the solvable fraction is `1`. No pigeonhole needed: the
adversary that returns `F.secret l i` is a perfectly good `Adversary`, it just is not one anybody can run.
The MLWE floor is the sharpest illustration of §8 — its `Eff := ⊤` form is unconditionally false. -/
theorem mlweHardQuant_top_false (F : MLWEFamily) : ¬ MLWEHardQuant F (fun _ => True) := by
  refine not_hard_top_of_always_solvable (mlweGame F) (fun l => ?_) (fun l i => ⟨F.secret l i, rfl⟩)
  show Nonempty (F.M l)
  letI := F.mGrp l
  exact ⟨0⟩

/-! ## §5 — discrete log: the challenge point IS the instance.

`SchnorrCurveField.SchnorrDLHard C G := ¬ ∃ solve, ∀ sk, solve (sk·G) = sk` is TRIVIALLY TRUE on any
finite group (`CryptoFloorTeeth.schnorrDLHard_of_smul_collision`) — its truth tracks injectivity of
`sk ↦ sk·G` over `ℕ`, a modelling artifact. The game asks the adversary to produce A discrete log of a
sampled challenge point, which is the actual problem. -/

/-- **A discrete-log instance family.** At each parameter a curve group with a generator, a finite space of
sampled scalars, and the exponent bound. The instance the adversary sees is the challenge POINT. -/
structure DLFamily where
  /-- The curve group at parameter `l`. -/
  C : ℕ → Dregg2.Crypto.SchnorrCurveField.CurveGroup
  /-- The generator at parameter `l`. -/
  gen : ∀ l, (C l).Pt
  /-- Decidable equality on points (the win event checks `x·G = P`). -/
  ptDec : ∀ l, DecidableEq ((C l).Pt)
  /-- The instance space: the sampled scalar's randomness. -/
  Inst : ℕ → Type
  /-- The instance space is finite. -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited. -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The sampled secret scalar at parameter `l`. -/
  sk : ∀ l, Inst l → ℕ

/-- The challenge point `P = sk·G` the adversary is given. -/
def DLFamily.chal (F : DLFamily) (l : ℕ) (i : F.Inst l) : (F.C l).Pt :=
  (F.C l).smul (F.sk l i) (F.gen l)

/-- **THE DISCRETE-LOG GAME.** The adversary WINS iff its output `x` is a discrete log of the challenge
point: `x·G = P`. Note it need not recover `sk` itself — ANY discrete log wins, which is the correct
statement (on a finite group `sk` is not unique, and demanding the sampled one is the modelling artifact
that makes `SchnorrDLHard` trivially true). -/
def dlGame (F : DLFamily) : Game where
  Inst := F.Inst
  Ans := fun _ => ℕ
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i x => (F.C l).smul x (F.gen l) = F.chal l i
  winsDec := fun l i x => F.ptDec l _ _

/-- **`DLHardQuant F Eff` — THE DISCRETE-LOG FLOOR, RESTATED.** Every `Eff`-adversary produces a discrete
log of a uniformly sampled challenge point only with negligible probability. -/
def DLHardQuant (F : DLFamily) (Eff : Adversary (dlGame F) → Prop) : Prop :=
  Hard (dlGame F) Eff

/-- **THE DL FLOOR IS FALSE AT THE UNRESTRICTED CLASS — always.** `sk l i` is itself a discrete log of the
challenge, so every instance is solvable. Again: no hardness assumption survives an unbounded adversary,
and the adversary here is not even exotic — it is "return the number that was used to build the
challenge". -/
theorem dlHardQuant_top_false (F : DLFamily) : ¬ DLHardQuant F (fun _ => True) :=
  not_hard_top_of_always_solvable (dlGame F) (fun _ => ⟨(0 : ℕ)⟩) (fun l i => ⟨F.sk l i, rfl⟩)

/-! ## §6 — hash collision resistance, and ⚑ THE REFUTATION OF THE SWEEP'S OWN PRESCRIBED REPAIR.

`VACUITY-SWEEP.md` §Finding-1's REPAIR says: *"`HashFloorHonesty.CollisionResistant` is the correct
pattern already in the tree — a keyed family whose `wins` predicate is definitionally a genuine collision
of the real function, so the advantage cannot be satisfied by an unrelated `adv`. The lattice floors need
the `CollisionResistant` treatment."*

Half of that is right: it carries its problem, and this file gives the lattice floors exactly that. The
other half is FALSE, and §2 proves it. `CollisionResistant F` quantified over ALL `CollisionFinder`s, and
a compressing family has a collision at every key, so the choice-finder wins with probability `1`. The
"proper computational floor" is FALSE at deployed parameters — the identical fate its own file proved for
the injective floors it replaced, reached by the identical pigeonhole, one `Classical.choice` later.

⚑ 2026-07-28: that `def` is DELETED (`HashFloorHonesty` §2 records what replaced it). It was the `⊤`
instance of THIS section's floor wearing a name, and the refutation, the satisfiability pole and the
injectivity bridge it carried are all restated below with `(fun _ => True)` written out. The past tense
above is deliberate: the object is gone, the finding stands. -/

open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv)

/-- **THE COLLISION GAME.** Instances are keys; answers are input pairs; the adversary WINS iff its pair is
a genuine collision — distinct inputs, equal hashes. This is `HashFloorHonesty.CollisionFinder.wins`
re-presented in the schema (`hashGame_wins_iff` pins the agreement). -/
def hashGame (F : KeyedHashFamily) : Game where
  Inst := F.Key
  Ans := fun _ => F.Input × F.Input
  instFin := F.keyFintype
  instNe := F.keyNonempty
  wins := fun l k p => p.1 ≠ p.2 ∧ F.H l k p.1 = F.H l k p.2
  winsDec := fun l k p => by
    letI := F.inputDecEq; letI := F.outDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the collision game's win relation is a genuine collision of the
real keyed function. -/
theorem hashGame_wins_iff (F : KeyedHashFamily) (l : ℕ) (k : F.Key l) (p : F.Input × F.Input) :
    (hashGame F).wins l k p ↔ (p.1 ≠ p.2 ∧ F.H l k p.1 = F.H l k p.2) :=
  Iff.rfl

/-- A `CollisionFinder` is an adversary against the collision game, and conversely. -/
def finderToAdv {F : KeyedHashFamily} (A : CollisionFinder F) : Adversary (hashGame F) where
  run := A.find

/-- The `CollisionFinder`'s win predicate and the game's `hit` agree pointwise. -/
theorem finderToAdv_hit {F : KeyedHashFamily} (A : CollisionFinder F) (l : ℕ) (k : F.Key l) :
    (finderToAdv A).hit l k = A.wins l k := by
  unfold Adversary.hit finderToAdv CollisionFinder.wins
  simp only [hashGame]
  by_cases h1 : (A.find l k).1 = (A.find l k).2 <;>
    by_cases h2 : F.H l k (A.find l k).1 = F.H l k (A.find l k).2 <;>
      simp [h1, h2]

/-- `HashFloorHonesty.collisionAdv` IS the game advantage. -/
theorem collisionAdv_eq_gameAdv {F : KeyedHashFamily} (A : CollisionFinder F) :
    collisionAdv F A = gameAdv (hashGame F) (finderToAdv A) := by
  funext l
  unfold collisionAdv gameAdv
  congr 1

/-- **`HashCRHardQuant F Eff` — THE HASH-CR FLOOR, RESTATED.** Every `Eff`-adversary finds a collision of
the keyed family under a uniformly sampled key only with negligible probability. -/
def HashCRHardQuant (F : KeyedHashFamily) (Eff : Adversary (hashGame F) → Prop) : Prop :=
  Hard (hashGame F) Eff

/-! ### ⚑ `HashFloorHonesty.CollisionResistant` WAS `HashCRHardQuant F ⊤`, AND IS DELETED (2026-07-28).

`collisionResistant_iff_hashCRHardQuant_top` proved the sweep's prescribed repair IS this floor at the
unrestricted class. That `↔` was the whole indictment, and once it is believed the `def` is a SPELLING
of `HashCRHardQuant F (fun _ => True)` that hides the `⊤` — which is precisely the field a reader has
to see to price the assumption. So the `def` is gone, the `↔` with it (an iff needs two sides), and
the four declarations that stood on it are restated below AT `⊤`, written out.

Nothing about the refutation is softened by the move; it is strengthened, because `⊤` no longer needs
a lemma to become visible. What IS lost is a census gate — see `Verify/FloorCensus.sentinelFloors`. -/

/-- **⚑ THE SWEEP'S PRESCRIBED REPAIR IS FALSE AT DEPLOYED PARAMETERS — THE TOOTH.** If the keyed family
is COMPRESSING — at every parameter and key some two distinct inputs collide, which is the defining
property of a hash and is forced by pigeonhole whenever `|Input| > |Out|` — then the collision floor at
the UNRESTRICTED class is FALSE.

The `Classical.choice` adversary that outputs a collision at every key is an `Adversary (hashGame F)`:
that structure bounds nothing. Its advantage is the constant `1`.

`HashFloorHonesty`'s own header says of its predecessor: *"the pre-existing non-vacuity witnesses give
FALSE COMFORT — they satisfy the floor with a toy injective sponge, while the REAL compressing Poseidon2
refutes it."* Its satisfiability tooth was the identity hash. `mod2Family` — its own example of a
genuinely compressing family — refutes this floor (below), though `mod2_dumb_negligible` shows only that
ONE dumb finder fails on it. The sentence applied to the successor, for the third time in a row, and is
why §3–§7 do not simply copy the pattern.

⚑ This is `collisionResistant_false_of_compressing` — the TOOTH — CARRIED THROUGH the deletion of its
old subject, not lost with it. Same proof, same content, `⊤` in the statement instead of behind a name. -/
theorem hashCRHardQuant_top_false_of_compressing (F : KeyedHashFamily) (hin : Nonempty F.Input)
    (hcol : ∀ l (k : F.Key l), ∃ x y : F.Input, x ≠ y ∧ F.H l k x = F.H l k y) :
    ¬ HashCRHardQuant F (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame F) (fun _ => ⟨(hin.some, hin.some)⟩) ?_
  intro l k
  obtain ⟨x, y, hne, heq⟩ := hcol l k
  exact ⟨(x, y), hne, heq⟩

/-- **THE SATISFIABLE POLE, AND ITS PRICE.** A per-key-INJECTIVE family has the `⊤`-class floor: no
adversary ever wins, so every advantage is `0`. Read with the tooth above this is the whole shape of the
`⊤` floor — it holds for injective families and fails for compressing ones, with nothing in between —
so a satisfiability witness at `⊤` is a statement that the family is not a hash.

⚑ Carries `HashFloorHonesty.injective_family_CR` through the deletion of `CollisionResistant`. -/
theorem hashCRHardQuant_top_of_injective (F : KeyedHashFamily)
    (hinj : ∀ l (k : F.Key l), Function.Injective (F.H l k)) :
    HashCRHardQuant F (fun _ => True) :=
  hard_top_of_never_solvable (hashGame F) (fun l k _p hp => hp.1 (hinj l k hp.2))

/-- **(TOOTH — SATISFIABLE, evaluated.)** The identity family has the `⊤`-class floor.
⚑ Carries `HashFloorHonesty.idFamily_CR`. -/
theorem idFamily_hashCRHardQuant_top :
    HashCRHardQuant Dregg2.Circuit.HashFloorHonesty.idFamily (fun _ => True) :=
  hashCRHardQuant_top_of_injective _ (fun _ _ _ _ h => h)

/-- **(TOOTH — REFUTABLE, evaluated.)** The broken (constant-`0`) family does NOT have the `⊤`-class
floor: `(0, 1)` collides at every key. So the floor is load-bearing, not vacuously true.
⚑ Carries `HashFloorHonesty.brokenFamily_not_CR`. -/
theorem brokenFamily_not_hashCRHardQuant_top :
    ¬ HashCRHardQuant Dregg2.Circuit.HashFloorHonesty.brokenFamily (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _ ⟨(0 : ℤ)⟩
    (fun _ _ => ⟨(0 : ℤ), (1 : ℤ), ?_, rfl⟩)
  show (0 : ℤ) ≠ (1 : ℤ)
  norm_num

/-- **THE REFUTATION FIRES ON A COMPRESSING FAMILY.** `HashFloorHonesty.mod2Family` (`H x = x % 2`) is the
tree's own example of a genuinely compressing hash — `mod2_collision_exists` exhibits the collision. So its
`⊤`-class floor is FALSE: `mod2_dumb_negligible` proved a DUMB finder has advantage `0`, which is true and
says nothing about the floor, because the floor quantifies over ALL adversaries including the one that
outputs `(0, 2)`. Satisfiable-by-a-toy, false-at-a-real-hash — the sweep's own diagnosis, applied to the
sweep's own repair. ⚑ Carries `mod2Family_not_CR`. -/
theorem mod2Family_not_hashCRHardQuant_top :
    ¬ HashCRHardQuant Dregg2.Circuit.HashFloorHonesty.mod2Family (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _ ⟨(0 : ℤ)⟩ (fun l k => ⟨(0 : ℤ), (2 : ℤ), ?_, ?_⟩)
  · show (0 : ℤ) ≠ (2 : ℤ)
    norm_num
  · simp [Dregg2.Circuit.HashFloorHonesty.mod2Family]

/-! ### §6.1 — ⚑ THE TWO ADVANTAGE-BOUNDED TEMPLATES, MOVED UP FROM RUNG 1 (2026-07-28).

`HashFloorHonesty.equivocation_advantage_negligible` and `.friFold_advantage_negligible` were the
only two declarations in the tree that CONSUMED `CollisionResistant` as a security hypothesis rather
than talking about it. Both are DELETED there and restated here at an EXPLICIT adversary class, which
is the whole difference between rung 1 and rung 2: `CollisionResistant F` WAS `HashCRHardQuant F ⊤`
(and is now DELETED in favour of writing that out) and `⊤` is refuted for every compressing family by the
theorem immediately above, so the two templates the FRI/STARK consumers were told to re-derive
through were conditioned on a hypothesis no deployed hash satisfies.

⚑ `Eff` IS THE RESIDUAL AND IT IS NOT DISCHARGED HERE. Its poles are priced in this file — `⊤` is
FALSE for a compressing family (`hashCRHardQuant_top_false_of_compressing`), `⊥` is vacuous
(`hard_bot_vacuous`), and `solvableIsAFiniteSearch` (§8) proves `Eff := Computable` cannot help
because what disqualifies brute force is COST, which this tree has no model of. The one class with a
PROVED bound is `RomQueryFloor.RomEff F Q` — query-bounded ROM adversaries, where
`RomQueryFloor.birthday_bound` gives `(Q²+1)/‖R‖` with no assumption at all and
`romEff_not_iff_solvableFrac_negl` proves the `⊤` collapse does NOT reach it. Instantiating these
templates there is a MODELLING step (a fixed keyed function is not a uniformly random oracle) and is
deliberately not taken silently. -/

/-- **THE ADVANTAGE-BOUNDED COMMITMENT BINDING, AT AN EXPLICIT CLASS.** An equivocation adversary —
one that, per key, opens one commitment to two DISTINCT reveals colliding under the hash — IS a
`CollisionFinder`; if it lies in the class `Eff`, the floor at `Eff` bounds its advantage. This is the
concrete-security form of `HermineHintMLWE.commitment_binding` / `FriSoundness.oracle_binding`: the
Boolean "opens ⟹ equal" becomes "opens ⟹ equal except with negligible probability". Unlike its
rung-1 predecessor the class membership is CARRIED IN THE OPEN, so a consumer cannot buy the bound
without saying which adversaries it is bounding. -/
theorem equivocation_advantage_negligible_eff {F : KeyedHashFamily}
    {Eff : Adversary (hashGame F) → Prop} (hHard : HashCRHardQuant F Eff)
    (A : CollisionFinder F) (hEff : Eff (finderToAdv A)) :
    Negl (collisionAdv F A) := by
  rw [collisionAdv_eq_gameAdv]
  exact hHard (finderToAdv A) hEff

/-- **THE ADDITIVE SOUNDNESS-ERROR COMBINATOR, AT AN EXPLICIT CLASS (the FRI/STARK template).** A
protocol with `rounds` Merkle-binding checks has total binding-failure advantage equal to the SUM of
the per-round collision advantages; if every round's finder lies in `Eff`, the total is negligible.
This is how a multi-round FRI/STARK chain re-derives on the honest floor — every per-round binding
use becomes an ADDITIVE negligible advantage term, threaded across rounds by `negl_finset_sum` — and
the per-round `Eff` obligation is now visible instead of hidden inside `⊤`. -/
theorem friFold_advantage_negligible_eff {F : KeyedHashFamily}
    {Eff : Adversary (hashGame F) → Prop} (rounds : Finset ℕ)
    (finder : ℕ → CollisionFinder F) (hHard : HashCRHardQuant F Eff)
    (hEff : ∀ r ∈ rounds, Eff (finderToAdv (finder r))) :
    Negl (fun n => ∑ r ∈ rounds, collisionAdv F (finder r) n) :=
  negl_finset_sum rounds (fun r hr =>
    (collisionAdv_eq_gameAdv (finder r)) ▸ hHard (finderToAdv (finder r)) (hEff r hr))

/-- **(TOOTH — the templates are NOT free.)** At the `⊥` class they hold vacuously, so a consumer that
never says which adversaries it bounds has bought nothing. Recorded beside the templates so the
`Eff`-shaped hole cannot be read as closed. -/
theorem hashCRHardQuant_bot_vacuous (F : KeyedHashFamily) :
    HashCRHardQuant F (fun _ => False) := hard_bot_vacuous (hashGame F)

/-! ## §7 — decisional MLWE: the LWE-vs-uniform gap, with both worlds PINNED.

`ProbCrypto.DecisionFamily` carries two arbitrary `Type`s and two arbitrary accept predicates — its "real
world" is not required to be an LWE sample and its "uniform world" is not required to be uniform. Its own
docstring says the *intended* `adv` is a `DecisionFamily.adv`; the sweep flagged exactly that word. Here
the real world IS `A·s + e` for a short secret and error, the uniform world IS the sample module, and the
distinguisher is ONE function applied to both — so the gap it measures is the LWE-vs-uniform gap. -/

/-- **A decisional-MLWE family.** The real world is an `MLWEFamily`'s keygen randomness; the uniform world
is the sample module itself, sampled uniformly. The distinguisher sees a sample module element in both
worlds and cannot tell which experiment produced it — that is what makes the two accept probabilities
comparable, and it is what the old `DecisionFamily` could not express. -/
structure MLWEDistFamily where
  /-- The underlying MLWE instance family (real world). -/
  base : MLWEFamily
  /-- The sample module is finite at each parameter (the uniform world is sampled from it). -/
  sampleFin : ∀ l, Fintype (base.N l)
  /-- The sample module is inhabited. -/
  sampleNe : ∀ l, Nonempty (base.N l)

/-- **A decisional distinguisher**: ONE accept predicate on sample-module elements, at each parameter. It
is applied to the real sample `A·s + e` and to a uniform element — the SAME function, which is what makes
`distinguishAdv` an LWE-vs-uniform gap rather than two unrelated numbers. -/
structure Distinguisher (F : MLWEDistFamily) where
  /-- The distinguisher's accept decision on a sample-module element. -/
  decide : ∀ l, F.base.N l → Bool

/-- The distinguisher's advantage: `|Pr[accept | A·s+e] − Pr[accept | uniform]|`, on
`ProbCrypto.distinguishAdv`. -/
noncomputable def distAdv (F : MLWEDistFamily) (D : Distinguisher F) : Ensemble := fun l =>
  @Dregg2.Crypto.ProbCrypto.distinguishAdv (F.base.Inst l) (F.base.N l)
    (F.base.instFin l) (F.sampleFin l)
    (fun i => D.decide l (F.base.pub l i))
    (fun t => D.decide l t)

/-- **`DecisionMLWEHardQuant F Eff` — THE DECISIONAL FLOOR, RESTATED.** Every `Eff`-distinguisher's
LWE-vs-uniform gap is negligible. The real world is pinned to genuine MLWE samples (`mlweFamily_isSample`)
and the uniform world to the sample module; the word "intended" no longer appears.

⚑ This floor does NOT ride the `Game` schema: a distinguishing advantage is a DIFFERENCE of two
probabilities, not a `winProb`, so §2's collapse does not apply to it — a distinguisher cannot appeal to
`Classical.choice` to know which world it is in. That asymmetry is real and it is the reason the decisional
floor is the healthiest of the five. It is still `Eff`-parameterized, because an unbounded distinguisher
that decides "is `t` of the form `A·s + e` for short `s`, `e`?" by exhaustive search has advantage close to
`1` whenever the sample space is not saturated. -/
def DecisionMLWEHardQuant (F : MLWEDistFamily) (Eff : Distinguisher F → Prop) : Prop :=
  ∀ D : Distinguisher F, Eff D → Negl (distAdv F D)

/-- The decisional advantage is a genuine probability gap in `[0,1]`. -/
theorem distAdv_mem_unit (F : MLWEDistFamily) (D : Distinguisher F) (l : ℕ) :
    0 ≤ distAdv F D l ∧ distAdv F D l ≤ 1 :=
  ⟨@Dregg2.Crypto.ProbCrypto.distinguishAdv_nonneg _ _ (F.base.instFin l) (F.sampleFin l) _ _,
   @Dregg2.Crypto.ProbCrypto.distinguishAdv_le_one _ _ (F.base.instFin l) (F.sampleFin l) _ _⟩

/-- **(TOOTH — the decisional floor is REFUTABLE.)** A distinguisher that accepts every real sample and no
uniform element has gap `1`, refuting the floor at any class containing it. Load-bearing, on a genuine
difference of probabilities. -/
theorem decisionMLWEHardQuant_refutable (F : MLWEDistFamily)
    (D : Distinguisher F)
    (hreal : ∀ l (i : F.base.Inst l), D.decide l (F.base.pub l i) = true)
    (hunif : ∀ l (t : F.base.N l), D.decide l t = false) :
    ¬ DecisionMLWEHardQuant F (fun _ => True) := by
  intro h
  have hD := h D trivial
  have hone : distAdv F D = fun _ => (1 : ℝ) := by
    funext l
    have hr : (fun i : F.base.Inst l => D.decide l (F.base.pub l i)) = (fun _ => true) := by
      funext i; exact hreal l i
    have hu : (fun t : F.base.N l => D.decide l t) = (fun _ => false) := by
      funext t; exact hunif l t
    show @Dregg2.Crypto.ProbCrypto.distinguishAdv _ _ (F.base.instFin l) (F.sampleFin l) _ _ = 1
    rw [hr, hu]
    unfold Dregg2.Crypto.ProbCrypto.distinguishAdv
    rw [@winProb_top _ (F.base.instFin l) (F.base.instNe l), @winProb_bot _ (F.sampleFin l)]
    norm_num
  rw [hone] at hD
  exact not_negl_one hD

/-! ## §8 — the residual, named: THE TREE HAS NO COST MODEL, and `Eff` is where that lives.

§2 proves the escape is `Eff` and only `Eff`. So: can `Eff` be given content HERE, over the definitions
this repository already has? The honest answer is no, and the two candidate answers fail for reasons worth
recording rather than rediscovering.

  * **Computability does not restrict the adversary.** Every instance space in every game above is a
    FINITE type, so "search all answers and return a winning one" is a total computable function of the
    instance. `Eff := Computable` therefore contains the choice adversary's computable twin and the floor
    stays false. The theorem below is the general form: a finite `Ans` makes the winner explicitly
    constructible with no choice at all.
  * **Polynomial time is not available.** Mathlib has no cost semantics over an arbitrary carrier — no
    `PPT`, no machine model, nothing to say `Eff A` means "A runs in time `poly(l)`". Stating it needs a
    deep embedding of the adversary (SSProve/EasyCrypt/FCF each carry one; this tree does not). That is
    the missing machinery, and inventing a shallow imitation of it here would be the fourth costume.

So the floors above are the standard cryptographic games **relative to an adversary class**, and the class
is a parameter with no content. That is strictly better than what they replace — the problem is in the
statement, the five floors are distinct, and the reductions must be exhibited — and it is strictly less
than a cryptographic assumption. Both halves of that sentence are load-bearing. -/

/-- **THE EXISTENCE OF A SOLUTION IS A FINITE SEARCH.** When the answer space is finite — and every
deployed one is: a lattice vector over a finite ring, a pair of hash inputs from a bounded domain, a
scalar below the group order — "does this instance have a solution?" is DECIDABLE, by exhaustive search
over `Ans l`. No oracle, no `Classical.choice`: the winner is found by looking.

This is the second half of §8's point, and it is why `Eff := Computable` cannot rescue the floor. The
adversary that brute-forces every instance is a perfectly ordinary total computable function; what
disqualifies it as an attack is that the search is ASTRONOMICALLY LARGE, and "large" is a statement about
COST. This tree can say `Fintype`; it cannot say `2^128`. That gap is the residual, and it is not a gap
this lane can close by restating anything. -/
def solvableIsAFiniteSearch (G : Game) (hfin : ∀ l, Fintype (G.Ans l)) (l : ℕ) (i : G.Inst l) :
    Decidable (∃ a, G.wins l i a) :=
  letI := hfin l
  letI : DecidablePred (G.wins l i) := G.winsDec l i
  Fintype.decidableExistsFintype

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  gameAdv_mem_unit,
  choiceAdv_gameAdv,
  gameAdv_le_solvableFrac,
  hard_top_iff_solvableFrac_negl,
  hard_bot_vacuous,
  not_hard_top_of_always_solvable,
  msisGame_wins_iff,
  msisHardQuant_top_false_of_compressing,
  mlweFamily_isSample,
  mlweHardQuant_top_false,
  dlHardQuant_top_false,
  hashGame_wins_iff,
  collisionAdv_eq_gameAdv,
  hard_top_of_never_solvable,
  hashCRHardQuant_top_false_of_compressing,
  hashCRHardQuant_top_of_injective,
  idFamily_hashCRHardQuant_top,
  brokenFamily_not_hashCRHardQuant_top,
  mod2Family_not_hashCRHardQuant_top,
  equivocation_advantage_negligible_eff,
  friFold_advantage_negligible_eff,
  hashCRHardQuant_bot_vacuous,
  distAdv_mem_unit,
  decisionMLWEHardQuant_refutable
]

end Dregg2.Crypto.FloorGames
