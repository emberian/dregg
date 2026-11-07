/-
# `Dregg2.Circuit.HashFloorHonesty` — the hash floors are INJECTIVITY, which is FALSE for a real
hash. FALSIFIABILITY TEETH + a PROPER computational collision-resistance floor.

## The bug this file documents (and forecloses)

The whole circuit-soundness tower conditions on hash floors stated as **injectivity**:

  * `Poseidon2Binding.Poseidon2SpongeCR sponge := ∀ xs ys, sponge xs = sponge ys → xs = ys`
  * `StateCommit.compressNInjective h`         (the same predicate on `List ℤ → ℤ`)
  * `StateCommit.compressInjective h := ∀ a b c d, h a b = h c d → a = c ∧ b = d`  (2-to-1)
  * `HermineHintMLWE.HashCR cr := ∀ i w w', cr.H i w = cr.H i w' → w = w'`         (commit-reveal)

Every one is **FALSE for any real hash**: a sponge maps an *infinite* domain (`List ℤ`, `ℤ × ℤ`, a
compressing `W`) into a *bounded* field element, so collisions **exist by cardinality / pigeonhole**.
Collision-resistance means collisions are hard to **FIND**, never that they don't **EXIST**. So every
theorem conditioned on one of these predicates is **VACUOUSLY TRUE at real parameters** — the
hypothesis is unsatisfiable. `#assert_axioms` is blind to it: the proofs are clean; the *hypothesis*
is the flaw.

The pre-existing "non-vacuity" witnesses (`FloorsNonVacuous.encodeSponge_cr`,
`Poseidon2Binding.Reference.refSponge_CR`) give FALSE COMFORT: they satisfy the floor with a **toy
injective** sponge (`Encodable.encode`, an injection into ALL of `ℤ`), while the REAL compressing
Poseidon2 refutes it. Toy witness satisfiable; real instantiation false.

## What this file provides

  * **§1 — FALSIFIABILITY TEETH.** The floors are proved **FALSE** for any range-bounded hash, by a
    cardinality / pigeonhole argument (`not_injective_of_finite_range` and its four specializations).
    You do NOT need an actual Poseidon2 collision — counting suffices, and is the honest statement.
    This is ember's "prove load-bearing specs true AND FALSE" discipline; nobody had tried to prove
    the floor FALSE, which is why the bug survived.

  * **§2 — THE KEYED COLLISION GAME** (`KeyedHashFamily`, `CollisionFinder`, `collisionAdv`): a
    **keyed** hash family indexed by the security parameter, and the advantage of a collision-finding
    adversary — the `winProb` that it outputs a genuine collision, over a uniformly random key.
    Keying is what makes the game meaningful: an unkeyed fixed hash lets an adversary hardcode a
    known collision (advantage `1`) — exactly the degeneracy that makes the OLD injective floor, and
    `FloorBridge`'s canonical collision family, collapse.

    ⚑ The FLOOR this section used to carry — `CollisionResistant F`, "every collision finder's
    advantage is `Negl`" — was DELETED on 2026-07-28, because §1's own argument applies to it: it
    quantifies over ALL finders, `Classical.choice` is one, and a compressing family therefore
    refutes it. The paragraph at the deletion site names every replacement. What is left in §2 is the
    GAME, which was never the problem, and the evaluated teeth (`mod2_dumb_negligible` exhibits
    collisions that exist while a specific finder's advantage is `0`) that keep the replacements in
    `FloorGames` §6 non-vacuous. The floor lives there now, with its adversary class written down.

  * **§3 — THE ADVANTAGE-BOUNDED RESTATEMENT.** Under proper CR the binding keystones survive as
    advantage bounds: an equivocating opener IS a collision finder, so "two openings ⟹ equal" becomes
    "⟹ equal EXCEPT with negligible probability" (now `FloorGames.equivocation_advantage_negligible_eff`); and a
    multi-round FRI/STARK soundness error is a finite SUM of per-round collision advantages, negligible
    by `negl_finset_sum` (now `FloorGames.friFold_advantage_negligible_eff`). This is the template every `HashCR` /
    `Poseidon2SpongeCR` consumer (`FriSoundness.oracle_binding`, `AirSoundness.committed_trace_pinned`,
    `FinBindsKernel`, the `StarkSound` chain) re-derives through — the Boolean "= equal" becomes a
    negligible advantage term, threaded additively.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; NO `sorryAx`/`sorry`, NO fresh `axiom`,
NO `def …Hard` used as a hypothesis. The proper floor is REFUTED on broken families and SATISFIED on
an injective one, so it is neither vacuous nor trivially true. NEW file; the old defs are KEPT
(doc-marked BROKEN beside the pointer to these teeth) — the record matters.
-/
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.StateCommit
import Dregg2.Crypto.HermineHintMLWE
import Dregg2.Crypto.ProbCrypto

namespace Dregg2.Circuit.HashFloorHonesty

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_bot)
open Dregg2.Crypto.ConcreteSecurity (Ensemble Negl negl_zero not_negl_one negl_add negl_finset_sum)

set_option autoImplicit false

/-! ## §1 — FALSIFIABILITY TEETH: the injective floors are FALSE for any range-bounded hash.

The core is a single cardinality fact: an INJECTIVE function from an INFINITE domain must have an
INFINITE range. A real hash's range is a bounded field, hence finite — contradiction. Every floor is
a specialization. -/

/-- **The counting core.** A function from an infinite type whose RANGE is finite is NOT injective.
(If it were, the corestriction to its range would inject the infinite domain into a finite set.) This
is the honest content behind "a compressing hash has collisions" — pure cardinality, no Poseidon2
collision exhibited. -/
theorem not_injective_of_finite_range {α β : Type*} [Infinite α] (f : α → β)
    (hfin : (Set.range f).Finite) : ¬ Function.Injective f := by
  intro hinj
  haveI : Finite (Set.range f) := hfin.to_subtype
  have hg : Function.Injective (fun a => (⟨f a, a, rfl⟩ : Set.range f)) :=
    fun a b h => hinj (congrArg Subtype.val h)
  haveI : Finite α := Finite.of_injective _ hg
  exact not_finite α

/-- `List ℤ` is infinite (the length-`n` all-zero lists are distinct). -/
instance : Infinite (List ℤ) :=
  Infinite.of_injective (fun n : ℕ => List.replicate n (0 : ℤ)) (fun n m h => by
    have := congrArg List.length h; simpa using this)

/-- **TOOTH 1 — `Poseidon2SpongeCR` is FALSE for a range-bounded sponge.** Any sponge that lands in a
finite set of field elements is non-injective on the infinite `List ℤ`, so it CANNOT satisfy the
injective floor. The REAL Poseidon2 sponge (into BabyBear, `|output| = p ≈ 2³¹`) is exactly such a
sponge — see `poseidon2SpongeCR_false_babyBear`. -/
theorem poseidon2SpongeCR_false_of_finite_range (sponge : List ℤ → ℤ)
    (hfin : (Set.range sponge).Finite) : ¬ Poseidon2SpongeCR sponge :=
  not_injective_of_finite_range sponge hfin

/-- **TOOTH 1′ — the same for `StateCommit.compressNInjective`** (the frame-sponge portal; literally
the same injectivity predicate on `List ℤ → ℤ`). -/
theorem compressNInjective_false_of_finite_range (h : List ℤ → ℤ)
    (hfin : (Set.range h).Finite) : ¬ compressNInjective h :=
  not_injective_of_finite_range h hfin

/-- A sponge whose output is a genuine field element `∈ [0, q)` has finite range (`⊆ Ico 0 q`). -/
theorem finite_range_of_field_bound (sponge : List ℤ → ℤ) (q : ℤ)
    (hb : ∀ xs, 0 ≤ sponge xs ∧ sponge xs < q) : (Set.range sponge).Finite := by
  refine (Set.finite_Ico (0 : ℤ) q).subset ?_
  rintro _ ⟨xs, rfl⟩
  exact ⟨(hb xs).1, (hb xs).2⟩

/-- **TOOTH 1 (deployed form) — the CR floor is FALSE at the REAL BabyBear parameters.** A sponge whose
output is a BabyBear field element (`0 ≤ · < p`, `p = 2³¹ − 2²⁷ + 1`) — i.e. every real Poseidon2
`hash_many` — refutes `Poseidon2SpongeCR`. The injective floor is not merely un-proven for the real
hash; it is provably FALSE there. -/
theorem poseidon2SpongeCR_false_babyBear (sponge : List ℤ → ℤ)
    (hb : ∀ xs, 0 ≤ sponge xs ∧ sponge xs < (2013265921 : ℤ)) : ¬ Poseidon2SpongeCR sponge :=
  poseidon2SpongeCR_false_of_finite_range sponge (finite_range_of_field_bound sponge _ hb)

/-- **TOOTH 2 — `StateCommit.compressInjective` is FALSE for a range-bounded 2-to-1 compression.** A
Poseidon2 node compress `ℤ × ℤ → ℤ` into a bounded field cannot be injective on the infinite `ℤ × ℤ`:
two field elements do not fit in one without collision. -/
theorem compressInjective_false_of_finite_range (h : ℤ → ℤ → ℤ)
    (hfin : (Set.range (fun p : ℤ × ℤ => h p.1 p.2)).Finite) : ¬ compressInjective h := by
  intro hci
  refine not_injective_of_finite_range (fun p : ℤ × ℤ => h p.1 p.2) hfin ?_
  rintro ⟨a, b⟩ ⟨c, d⟩ heq
  obtain ⟨h1, h2⟩ := hci a b c d heq
  simp [h1, h2]

/-- **TOOTH 3 — `HashCR` is FALSE for a COMPRESSING commit-reveal.** If the committed domain `W` is
larger than the commitment space `C` (`|C| < |W|` — the defining property of a commitment/compression),
then at every index the hash pins two distinct reveals to one commitment (pigeonhole). So a real
compressing commit-reveal refutes the injective `HashCR` floor. -/
theorem hashCR_false_of_compressing {Idx W C : Type*} [Fintype W] [Fintype C]
    (cr : CommitReveal Idx W C) (i : Idx) (hcard : Fintype.card C < Fintype.card W) :
    ¬ HashCR cr := by
  obtain ⟨w, w', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (cr.H i) hcard
  exact fun hCR => hne (hCR i w w' heq)

/-! ## §2 — PROPER computational collision-resistance (a REAL, satisfiable, non-trivial floor).

The honest replacement for injectivity: a KEYED hash family and an advantage that measures the
adversary *finding* a collision over a uniformly random key. The key (realized in the deployed system
by domain separation and the security-parameter growth) is what stops the "hardcode a known collision"
degeneracy that collapses the unkeyed injective floor. -/

/-- A **keyed hash family**: at each security parameter `n` a finite, inhabited key space `Key n` and a
hash `H n : Key n → Input → Out`. (The deployed Poseidon2 is unkeyed; its effective key is the
domain-separation tag / parameter regime — the honest place the concrete-security game lives.) -/
structure KeyedHashFamily where
  /-- Key space at security parameter `n`. -/
  Key : ℕ → Type
  /-- Hash input domain (`List ℤ` for the sponge, `W` for a commit-reveal). -/
  Input : Type
  /-- Hash output (the bounded field element / commitment). -/
  Out : Type
  /-- The keyed hash. -/
  H : ∀ n, Key n → Input → Out
  /-- Each key space is finite (the game samples a uniform key). -/
  keyFintype : ∀ n, Fintype (Key n)
  /-- Each key space is inhabited (non-empty outcome space). -/
  keyNonempty : ∀ n, Nonempty (Key n)
  /-- Decidable equality on inputs (to check `x ≠ x'`). -/
  inputDecEq : DecidableEq Input
  /-- Decidable equality on outputs (to check the hashes collide). -/
  outDecEq : DecidableEq Out

/-- A **collision finder**: for each parameter and key it outputs a candidate collision pair. Its
success is a function of the key — it does NOT get to depend on a collision handed to it, which is what
makes finding hard for a real hash. -/
structure CollisionFinder (F : KeyedHashFamily) where
  /-- The candidate collision the finder outputs on key `k`. -/
  find : ∀ n, F.Key n → F.Input × F.Input

/-- The finder **wins** on key `k` iff its two outputs are DISTINCT yet hash EQUAL — a genuine
collision. -/
def CollisionFinder.wins {F : KeyedHashFamily} (A : CollisionFinder F) (n : ℕ) (k : F.Key n) : Bool :=
  letI := F.inputDecEq
  letI := F.outDecEq
  let p := A.find n k
  decide (p.1 ≠ p.2) && decide (F.H n k p.1 = F.H n k p.2)

/-- The finder's **advantage ensemble**: at parameter `n`, the `winProb` — the fraction of keys on
which it outputs a genuine collision. A real number in `[0,1]`, exactly the concrete-security object.
(The `Fintype` instance is supplied explicitly from the family field so downstream proofs can name the
exact instance the ensemble is stated against.) -/
noncomputable def collisionAdv (F : KeyedHashFamily) (A : CollisionFinder F) : Ensemble :=
  fun n => @winProb (F.Key n) (F.keyFintype n) (fun k : F.Key n => A.wins n k)

/-! ⚑ **DELETED 2026-07-28 — `def CollisionResistant`, and with it `brokenFamily_not_CR`,
`idFamily_CR` and `injective_family_CR`.**

`CollisionResistant F := ∀ A : CollisionFinder F, Negl (collisionAdv F A)` was this file's
"proper computational floor", the honest replacement §1 refutes the injective floors in favour of.
It was itself REFUTED: `FloorGames.collisionResistant_iff_hashCRHardQuant_top` proved it IS the
collision game's floor at the UNRESTRICTED adversary class, and
`FloorGames.collisionResistant_false_of_compressing` proved that class's floor FALSE for EVERY
compressing family — `Classical.choice` is a perfectly good `CollisionFinder`. Three costumes in,
the same pigeonhole. So the floor is gone and the `⊤` it silently was is now spelled out at every
site that used to hide it.

WHAT REPLACES IT, all in `Crypto/FloorGames` §6 with the adversary class IN THE STATEMENT:

  * `hashCRHardQuant_top_of_injective`      ← `injective_family_CR`
  * `idFamily_hashCRHardQuant_top`          ← `idFamily_CR`             (SATISFIABLE pole)
  * `brokenFamily_not_hashCRHardQuant_top`  ← `brokenFamily_not_CR`     (REFUTABLE pole)
  * `hashCRHardQuant_top_false_of_compressing` ← `collisionResistant_false_of_compressing`
    — ⚑ the TOOTH SURVIVES. Its subject moved from `CollisionResistant F` to the propositionally
    equal `HashCRHardQuant F (fun _ => True)`, which is strictly more honest: the refuted `⊤` is
    now written down instead of being folded into a name.

The GAME OBJECTS below (`KeyedHashFamily`, `CollisionFinder`, `collisionAdv`, `brokenFamily`,
`idFamily`, `mod2Family` and their evaluated lemmas) are KEPT: `FloorGames.hashGame` is built on
them and they were never the problem. The adversary CLASS was.

⚑ THE GATE THIS COST — see `Verify/FloorCensus.sentinelFloors`. -/

/-! ### Teeth: the families are REFUTABLE, SATISFIABLE, and genuinely computational.

The floor-typed halves of these teeth now live in `FloorGames` §6 (above); what remains here is the
EVALUATED half — which finder wins on which family — which is what makes those ports non-vacuous. -/

/-- The **broken** (constant-`0`) family — every input hashes to `0`, so ANY two distinct inputs
collide. -/
def brokenFamily : KeyedHashFamily where
  Key := fun _ => Unit
  Input := ℤ
  Out := ℤ
  H := fun _ _ _ => 0
  keyFintype := fun _ => inferInstance
  keyNonempty := fun _ => inferInstance
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- A finder that always outputs the distinct pair `(0, 1)` — a genuine collision under `brokenFamily`. -/
def brokenFinder : CollisionFinder brokenFamily where
  find := fun _ _ => ((0, 1) : ℤ × ℤ)

theorem brokenFinder_wins (n : ℕ) (k : brokenFamily.Key n) : brokenFinder.wins n k = true := by
  simp [CollisionFinder.wins, brokenFinder, brokenFamily]

/-- **(THE EVALUATED HALF OF THE REFUTABILITY TOOTH.)** The constant finder's advantage on the broken
family is the constant `1`. `FloorGames.brokenFamily_not_hashCRHardQuant_top` is the floor-typed half
that reads `not_negl_one` off this. -/
theorem brokenFinder_adv_one : collisionAdv brokenFamily brokenFinder = fun _ => (1 : ℝ) := by
  funext n
  have hall : (fun k : brokenFamily.Key n => brokenFinder.wins n k) = (fun _ => true) := by
    funext k; exact brokenFinder_wins n k
  show @winProb (brokenFamily.Key n) (brokenFamily.keyFintype n)
      (fun k : brokenFamily.Key n => brokenFinder.wins n k) = 1
  rw [hall]
  exact @winProb_top (brokenFamily.Key n) (brokenFamily.keyFintype n) (brokenFamily.keyNonempty n)

/-- The **injective identity** family — `H n k x = x`, no collisions exist at all. -/
@[reducible] def idFamily : KeyedHashFamily where
  Key := fun _ => Unit
  Input := ℤ
  Out := ℤ
  H := fun _ _ x => x
  keyFintype := fun _ => inferInstance
  keyNonempty := fun _ => inferInstance
  inputDecEq := inferInstance
  outDecEq := inferInstance

theorem idFamily_wins_false (A : CollisionFinder idFamily) (n : ℕ) (k : idFamily.Key n) :
    A.wins n k = false := by
  simp only [CollisionFinder.wins, idFamily]
  by_cases hp : (A.find n k).1 = (A.find n k).2 <;> simp [hp]

/-- The **mod-2** family — `H n k x = x % 2`, a genuine COMPRESSING hash: collisions EXIST (e.g. `0`
and `2` both hash to `0`) for every key. -/
def mod2Family : KeyedHashFamily where
  Key := fun _ => Unit
  Input := ℤ
  Out := ℤ
  H := fun _ _ x => x % 2
  keyFintype := fun _ => inferInstance
  keyNonempty := fun _ => inferInstance
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- Collisions genuinely EXIST in `mod2Family`: `0 ≠ 2` yet both hash to `0`. -/
theorem mod2_collision_exists (n : ℕ) (k : mod2Family.Key n) :
    (0 : ℤ) ≠ 2 ∧ mod2Family.H n k (0 : ℤ) = mod2Family.H n k (2 : ℤ) := by
  refine ⟨by norm_num, ?_⟩
  simp [mod2Family]

/-- A **dumb** finder that outputs the NON-colliding distinct pair `(0, 1)` (`0 % 2 = 0`, `1 % 2 = 1`). -/
def dumbFinder : CollisionFinder mod2Family where
  find := fun _ _ => ((0, 1) : ℤ × ℤ)

/-- **(TOOTH — advantage measures FINDING, not EXISTENCE.)** Even though collisions EXIST in
`mod2Family` (`mod2_collision_exists`), the dumb finder that fails to output one has advantage `0`,
hence negligible. This is exactly what the OLD injective floor (and `FloorBridge`'s canonical
collision family, whose "a collision exists ⇒ advantage `1`" conflation reproduced the vacuity) got
wrong: existence of a collision does NOT by itself break computational CR. The advantage is a genuine
function of whether the adversary FINDS the collision. -/
theorem mod2_dumb_negligible : Negl (collisionAdv mod2Family dumbFinder) := by
  have hadv : collisionAdv mod2Family dumbFinder = fun _ => (0 : ℝ) := by
    funext n
    have hall : (fun k : mod2Family.Key n => dumbFinder.wins n k) = (fun _ => false) := by
      funext k; simp [CollisionFinder.wins, dumbFinder, mod2Family]
    show @winProb (mod2Family.Key n) (mod2Family.keyFintype n)
        (fun k : mod2Family.Key n => dumbFinder.wins n k) = 0
    rw [hall]
    exact @winProb_bot (mod2Family.Key n) (mod2Family.keyFintype n)
  rw [hadv]; exact negl_zero

/-! ### The bridge to the old floor: injectivity is STRICTLY STRONGER — and FALSE.

A per-key-injective family has no collisions at all, so every finder's advantage is `0`. That was
`injective_family_CR : … → CollisionResistant F`; with the floor deleted it is
`FloorGames.hashCRHardQuant_top_of_injective : … → HashCRHardQuant F (fun _ => True)`, same content,
`⊤` spelled out. The point it was making SURVIVES the deletion and is worth restating, because it is
what dooms both floors together: injectivity is FALSE for the real hash (§1), and the `⊤`-class
collision floor is satisfied by essentially nothing else (`FloorGames`
`hashCRHardQuant_top_false_of_compressing`: any family with a collision at every key refutes it). A
floor whose only witnesses are injective families is not a weaker assumption than injectivity, it is
the same false comfort with an advantage in front of it. -/

/-! ## §3 — the ADVANTAGE-BOUNDED restatement of the binding keystones.

Under proper CR the Boolean "two openings ⟹ equal" (`commitment_binding`, `oracle_binding`) restates
as "⟹ equal EXCEPT with negligible probability": an equivocating opener IS a collision finder, so its
success is negligible. And a multi-round FRI/STARK soundness error is a finite SUM of per-round
collision advantages, negligible by `negl_finset_sum`. -/

/-! ⚑ **DELETED 2026-07-28 — `equivocation_advantage_negligible` and `friFold_advantage_negligible`.**

They were the only two declarations in the tree that CONSUMED `CollisionResistant` as a security
hypothesis rather than talking about it, and both were conditioned on a floor this tree REFUTES:
`FloorGames.collisionResistant_iff_hashCRHardQuant_top` proves `CollisionResistant F` IS the collision
floor at the UNRESTRICTED adversary class, and `FloorGames.collisionResistant_false_of_compressing`
proves that class's floor FALSE for EVERY compressing family — one `Classical.choice` collision finder
later. So "the template every `HashCR` / `Poseidon2SpongeCR` consumer re-derives through" had a
hypothesis no deployed hash satisfies, which is the identical fate §1 proves for the injective floors
this section was written to replace.

REPLACED, in the same commit, by `FloorGames.equivocation_advantage_negligible_eff` and
`.friFold_advantage_negligible_eff` — the same two statements at an EXPLICIT adversary class
`Eff`, with the class membership carried in the open. They live in `FloorGames` because
`HashCRHardQuant` is defined there and that module imports this one. Neither had a single Lean
consumer in this tree, so the move costs nothing but the honesty of the hypothesis. `Eff` is
undischarged and its poles are priced beside the replacements; the one class with a PROVED bound is
`RomQueryFloor.RomEff`. -/

/-! ## §4 — axiom-hygiene tripwires. -/

#assert_axioms not_injective_of_finite_range
#assert_axioms poseidon2SpongeCR_false_babyBear
#assert_axioms compressInjective_false_of_finite_range
#assert_axioms hashCR_false_of_compressing
#assert_axioms brokenFinder_adv_one
#assert_axioms idFamily_wins_false
#assert_axioms mod2_dumb_negligible

end Dregg2.Circuit.HashFloorHonesty
