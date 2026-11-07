/-
# `Dregg2.Crypto.HermineRomBinding` — the Hermine COMMIT-REVEAL binding, RE-GROUNDED on the KEYED,
QUERY-COUNTED random-oracle floor (the PROVED floor), and the concurrent rushing composition with its
equivocation horn DISCHARGED there.

## What this replaces (the D-class drop)

`HermineHintMLWE.commitment_binding` and `HermineHintMLWE.concurrent_unforgeable_reduces` carried
`hcr : HashCR cr` — pure INJECTIVITY of the commit map, PROVED FALSE for every compressing
commit-reveal by `HashFloorHonesty.hashCR_false_of_compressing`. Both are DELETED (same commit as this
file). Their content survives as:

  * the deterministic extractor `HermineHintMLWE.equivocation_breaks_hashcr` (an equivocated opening
    IS a collision — a `¬ HashCR` conclusion, retained ONLY as the reduction's witness, never
    re-exported as a floor);
  * the rushing dichotomy `HermineHintMLWE.concurrent_forgery_breaks_hashcr_or_msis` (no floor
    hypothesis — the case split itself);
  * the probabilistic keystone `HermineHashCRRegrounded.hermine_concurrent_forgery_advantage_bound`
    (both horns' floors PARAMETRIC); and
  * **THIS FILE**: the binding and the equivocation horn discharged on `KeyedRomFloor.keyedRom_hard`
    — the birthday bound, a THEOREM, with the counterexample (a hardcoded collision answerer)
    ADMITTED and DEFANGED rather than assumed away.

Why a separate module and not a §8 of `HermineHashCRRegrounded`: `Crypto.RomCarrierSites` (the per-site
keyed-ROM kit) already IMPORTS `HermineHashCRRegrounded` (for `winProb_le_add_of_imp`), so the ROM
successors cannot live there without an import cycle.

## ⚑ The modelling step, stated (not smuggled)

Exactly `RomCarrierSites`' header: the deployed commit hash `cmᵢ = H(i, wᵢ)` is idealised as ONE
SAMPLED keyed oracle `H : Idx × W → Fin (2 ^ l)` — the standard ROM idealisation of the
domain-separated hash at an ASYMPTOTIC digest width, a deliberate labelled modelling step, NOT a
derivation about the fixed deployed function. What it buys: the floor under the binding is
`keyedRom_hard` (PROVED) where the deleted export carried a hypothesis that is FALSE. What it does not
buy: any statement about the fixed public hash itself.

## Non-fake

The `shortCollAdv` shape — a `0`-query answerer with a hardcoded "collision" — is IN the class
(`constTriple_in_eff`), wins with POSITIVE probability (`crRom_class_inhabited_pos`), and its
advantage is NEGLIGIBLE (`crRom_constAnswer_defanged`): the counterexample DIES under keying instead
of being excluded by fiat. A non-negligible equivocator is OUTSIDE the class
(`crRom_nonNegl_forger_excluded`). The §5 canary proves the floor at ANOTHER adversary does not close
the bound. `#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no `axiom`, no
`native_decide`.
-/
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.HermineRomBinding

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.FloorGames
  (Game Adversary Hard gameAdv gameAdv_mem_unit msisGame MSISHardQuant)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor (RomEff)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily keyedRomGame KeyedRomEff keyedRom_hard)
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomCarrierSites
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineHashCRRegrounded
  (ConcurrentForgeryFamily concurrentForgeryGame cfEquivGame cfMsisFamily
   forgeryToMsisSolver forgeryToEquivFinder hermine_concurrent_forgery_advantage_bound)

set_option autoImplicit false

/-! ## §1 — the commit-reveal keyed ROM family and its carrier.

The deployed commitment is `cmᵢ = H(i, wᵢ)`: the signer index `i` is the domain-separation tag (the
KEY coordinate of the sampled oracle) and the reveal `w` is the absorbed message. The carrier's
per-site content — the encoding and its payload-injectivity — is trivial here because the absorbed
message IS the reveal. -/

variable (Idx : Type) [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
variable (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]

/-- **THE COMMIT-REVEAL KEYED ROM FAMILY** — keyed by the signer index (the deployed domain
separation), messages = the reveals, ideal `λ`-bit digest. -/
def crRomFamily : KeyedRomFamily :=
  flatFamily Idx inferInstance inferInstance inferInstance (fun _ => W)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)

/-- The family's width obligation, closed by construction. -/
theorem crRomFamily_card_R (l : ℕ) :
    letI := (crRomFamily Idx W).rFin l
    Fintype.card ((crRomFamily Idx W).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE COMMIT-REVEAL CARRIER** — commitment `H (i, w)`; the encoding is the identity in the
payload, injective on the nose (the ROM restatement of "the commit absorbs the reveal verbatim"). -/
def crRomCarrier : RomCarrier (crRomFamily Idx W) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => W) (fun _ => inferInstance)
    (fun _ _ w => w) (fun _ _ _ _ h => h)

/-- The commit-reveal opening-equivocation game at the sampled keyed oracle. -/
abbrev crRomGame : Game := romCarrierGame (crRomFamily Idx W) (crRomCarrier Idx W)

/-- **THE DEPLOYED EQUIVOCATION IS A WIN.** Two DISTINCT reveals whose tagged messages the sampled
oracle maps to ONE commitment are a win of the game — `equivocation_breaks_hashcr`, restated at the
sampled oracle. -/
theorem crRom_equivocation_is_break (l : ℕ) (H : (crRomGame Idx W).Inst l) (i : Idx)
    {w w' : W} (hne : w ≠ w') (heq : H (i, w) = H (i, w')) :
    (crRomGame Idx W).wins l H ((i, ()), w, w') :=
  ⟨hne, heq⟩

/-- **⚑⚑ THE COMMIT-REVEAL BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the deleted
`HermineHintMLWE.commitment_binding`: every query-bounded forger that opens one commitment with two
distinct reveals has NEGLIGIBLE advantage, in the keyed ROM model of the header. The hypotheses are a
polynomial query budget and the forger's membership in the query class — nothing refutable. -/
theorem commitReveal_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (crRomGame Idx W))
    (hA : RomCarrierEff (crRomFamily Idx W) (crRomCarrier Idx W) Q A) :
    Negl (gameAdv (crRomGame Idx W) A) :=
  romCarrier_binds _ _ Q hQ (crRomFamily_card_R Idx W) A hA

/-! ### Non-vacuity teeth — the counterexample DIES here (admitted, defanged, not excluded). -/

/-- **(TOOTH — the class is INHABITED with POSITIVE advantage.)** The `0`-query constant answerer on
two distinct reveals is in the class at every budget and wins with positive probability at every
parameter. -/
theorem crRom_class_inhabited_pos (Q : ℕ → ℕ) (i : Idx) {w w' : W} (hne : w ≠ w') :
    ∃ A, RomCarrierEff (crRomFamily Idx W) (crRomCarrier Idx W) Q A
      ∧ ∀ l, 0 < gameAdv (crRomGame Idx W) A l :=
  ⟨romCarrierAdv _ _ (constTripleComp _ _ (fun _ => (i, ())) (fun _ => w) (fun _ => w')),
    constTriple_in_eff _ _ _ _ _ Q,
    fun l => constTriple_gameAdv_pos _ _ _ _ _ l hne⟩

/-- **(TOOTH — the `shortCollAdv` shape is ADMITTED and DEFANGED.)** The exact answerer shape that
refutes the injective `HashCR` floor — a `0`-query hardcoded pair — is in the query class, and its
advantage against the SAMPLED oracle is NEGLIGIBLE, where against the fixed compressing hash it wins
with probability `1`. The counterexample dies by keying, not by exclusion. -/
theorem crRom_constAnswer_defanged (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (c : ∀ l, (crRomCarrier Idx W).Ctx l) (v w : ∀ l, (crRomCarrier Idx W).Val l) :
    Negl (gameAdv (crRomGame Idx W) (romCarrierAdv _ _ (constTripleComp _ _ c v w))) :=
  constTriple_binds _ _ c v w Q hQ (crRomFamily_card_R Idx W)

/-- **(TOOTH — a non-negligible forger is OUTSIDE the class.)** The refutation strategy that killed
the injective floor cannot produce a member of this one. -/
theorem crRom_nonNegl_forger_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (crRomGame Idx W))
    (hnn : ¬ Negl (gameAdv (crRomGame Idx W) A)) :
    ¬ RomCarrierEff (crRomFamily Idx W) (crRomCarrier Idx W) Q A :=
  romCarrier_choiceForger_excluded _ _ Q hQ (crRomFamily_card_R Idx W) A hnn

/-! ## §2 — the CONCURRENT rushing composition, its equivocation horn on the PROVED floor.

`HermineHashCRRegrounded` §3–§4 already makes the rushing forger a first-class `Game`
(`concurrentForgeryGame`) and proves the union-bound keystone
`hermine_concurrent_forgery_advantage_bound` with BOTH horns' floors parametric. Here the family is
INSTANTIATED at the sampled keyed oracle — the instance space IS the oracle space, the commit map IS
the oracle — and the equivocation horn's floor `Hard (cfEquivGame _) _` is PROVED from
`keyedRom_hard`. The MSIS horn stays at the honest adversary-quantified `MSISHardQuant` (the lattice
floor is not this campaign's; the Boolean `MSISHard` the deleted export carried is itself an
existence-refutation, `Lattice.MSISHard`'s own docstring). -/

section Concurrent

variable {Rq : Type} [CommRing Rq] [ShortNorm Rq] [DecidableEq Rq]
variable {M : Type} [AddCommGroup M] [Module Rq M] [ShortNorm M] [DecidableEq M]
variable {N : Type} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable [Fintype N] [DecidableEq N] [Nonempty N]

/-- **THE CONCURRENT-FORGERY FAMILY AT THE SAMPLED KEYED ORACLE.** The instance space is the oracle
space of `crRomFamily Idx N`; the commit map is the ORACLE at the fixed signer tag `i₀`; the target
commitment is the honest signer's `H (i₀, wH)`. The algebraic data `(A₀, t₀, β₀)` is the deployed
SelfTargetMSIS instance, fixed across oracles. -/
def cfRomFamily (A₀ : M →ₗ[Rq] N) (t₀ : N) (i₀ : Idx) (wH : N) (β₀ : ℕ) :
    ConcurrentForgeryFamily where
  Rq := fun _ => Rq
  M := fun _ => M
  N := fun _ => N
  C := fun l => Fin (2 ^ l)
  rqRing := fun _ => inferInstance
  rqNrm := fun _ => inferInstance
  rqDec := fun _ => inferInstance
  mGrp := fun _ => inferInstance
  mMod := fun _ => inferInstance
  mNrm := fun _ => inferInstance
  mDec := fun _ => inferInstance
  nGrp := fun _ => inferInstance
  nMod := fun _ => inferInstance
  nNrm := fun _ => inferInstance
  nDec := fun _ => inferInstance
  cDec := fun _ => inferInstance
  Inst := fun l => (crRomFamily Idx N).toRomFamily.D l → (crRomFamily Idx N).toRomFamily.R l
  instFin := fun l =>
    (Dregg2.Crypto.RomQueryFloor.romCollisionGame (crRomFamily Idx N).toRomFamily).instFin l
  instNe := fun l =>
    (Dregg2.Crypto.RomQueryFloor.romCollisionGame (crRomFamily Idx N).toRomFamily).instNe l
  A := fun _ _ => A₀
  t := fun _ _ => t₀
  commit := fun _ H w => H (i₀, w)
  cmt := fun _ H => H (i₀, wH)
  β := fun _ => β₀

/-- **THE QUERY-BOUNDED EQUIVOCATION-HORN CLASS** — an adversary of the equivocation game factors
through a `Q`-query oracle tree over the tag-separated domain, fixed BEFORE the oracle is sampled. -/
def CfEquivRomEff (A₀ : M →ₗ[Rq] N) (t₀ : N) (i₀ : Idx) (wH : N) (β₀ : ℕ) (Q : ℕ → ℕ)
    (A : Adversary (cfEquivGame (cfRomFamily Idx A₀ t₀ i₀ wH β₀))) : Prop :=
  ∃ Mt : ∀ l, OracleComp ((crRomFamily Idx N).toRomFamily.D l)
      ((crRomFamily Idx N).toRomFamily.R l) (N × N),
    (∀ l, QueryBounded (Q l) (Mt l)) ∧
      ∀ l (H : (cfEquivGame (cfRomFamily Idx A₀ t₀ i₀ wH β₀)).Inst l),
        A.run l H = (Mt l).eval H

/-- **⚑ THE EQUIVOCATION HORN'S FLOOR, PROVED.** At the sampled keyed oracle the commit-collision
game is `Hard` for the query-bounded class: a collision of `H (i₀, ·)` is a collision of the sampled
oracle, and the birthday bound (`keyedRom_hard`) closes it. This is the hypothesis
`hcol : Hard (cfEquivGame F) EffH` of the repaired keystone, DISCHARGED — where the deleted
`concurrent_unforgeable_reduces` assumed the refuted injective `HashCR` for the same horn. -/
theorem cfEquivRom_hard (A₀ : M →ₗ[Rq] N) (t₀ : N) (i₀ : Idx) (wH : N) (β₀ : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    Hard (cfEquivGame (cfRomFamily Idx A₀ t₀ i₀ wH β₀)) (CfEquivRomEff Idx A₀ t₀ i₀ wH β₀ Q) := by
  intro A hA
  obtain ⟨Mt, hMQ, hrun⟩ := hA
  -- the extracted keyed collision finder: tag both reveals with the fixed signer index.
  let B : Adversary (keyedRomGame (crRomFamily Idx N)) :=
    ⟨fun l H => ((i₀, (A.run l H).1), (i₀, (A.run l H).2))⟩
  have hle : ∀ l, gameAdv (cfEquivGame (cfRomFamily Idx A₀ t₀ i₀ wH β₀)) A l
      ≤ gameAdv (keyedRomGame (crRomFamily Idx N)) B l := by
    intro l
    refine @winProb_le_of_imp _
      ((cfEquivGame (cfRomFamily Idx A₀ t₀ i₀ wH β₀)).instFin l) _ _ (fun H hH => ?_)
    replace hH := (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mp hH
    refine (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mpr ?_
    obtain ⟨hne, heq⟩ := hH
    exact ⟨fun hc => hne (congrArg Prod.snd hc), heq⟩
  have hB : RomEff (crRomFamily Idx N).toRomFamily Q B := by
    refine ⟨fun l => OracleComp.mapOut (fun p : N × N => ((i₀, p.1), (i₀, p.2))) (Mt l),
      fun l => OracleComp.mapOut_queryBounded _ (hMQ l), ?_⟩
    intro l H
    show ((i₀, (A.run l H).1), (i₀, (A.run l H).2)) = _
    erw [OracleComp.mapOut_eval, hrun l H]
    rfl
  exact negl_of_le
    (fun l => (gameAdv_mem_unit (cfEquivGame (cfRomFamily Idx A₀ t₀ i₀ wH β₀)) A l).1)
    hle (keyedRom_hard (crRomFamily Idx N) Q hQ (crRomFamily_card_R Idx N) B hB)

/-- **⚑⚑ THE CONCURRENT RUSHING BOUND, EQUIVOCATION HORN ON THE PROVED FLOOR** — the successor of the
deleted `HermineHintMLWE.concurrent_unforgeable_reduces`. A rushing forger — it opens the honest
commitment `H (i₀, wH)` with two reveals and outputs two accepting SelfTargetMSIS solutions with
`c ≠ c'` — has NEGLIGIBLE advantage, provided: the extracted MSIS solver is in the class the
adversary-quantified lattice floor `MSISHardQuant` quantifies over (the honest, parametric state of
the lattice horn), and the extracted equivocator is query-bounded (its floor is then PROVED, by
`cfEquivRom_hard`). The deleted export instead carried `HashCR` (refuted) AND the Boolean existence
floor `MSISHard` (an existence-refutation, false at deployment); neither survives here. -/
theorem hermine_concurrent_forgery_rom (A₀ : M →ₗ[Rq] N) (t₀ : N) (i₀ : Idx) (wH : N) (β₀ : ℕ)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (Eff : Adversary (msisGame (cfMsisFamily (cfRomFamily Idx A₀ t₀ i₀ wH β₀))) → Prop)
    (A : Adversary (concurrentForgeryGame (cfRomFamily Idx A₀ t₀ i₀ wH β₀)))
    (hEff : Eff (forgeryToMsisSolver (cfRomFamily Idx A₀ t₀ i₀ wH β₀) A))
    (hEffH : CfEquivRomEff Idx A₀ t₀ i₀ wH β₀ Q
      (forgeryToEquivFinder (cfRomFamily Idx A₀ t₀ i₀ wH β₀) A))
    (hmsis : MSISHardQuant (cfMsisFamily (cfRomFamily Idx A₀ t₀ i₀ wH β₀)) Eff) :
    Negl (gameAdv (concurrentForgeryGame (cfRomFamily Idx A₀ t₀ i₀ wH β₀)) A) :=
  hermine_concurrent_forgery_advantage_bound (cfRomFamily Idx A₀ t₀ i₀ wH β₀)
    Eff (CfEquivRomEff Idx A₀ t₀ i₀ wH β₀ Q) A hEff hEffH hmsis
    (cfEquivRom_hard Idx A₀ t₀ i₀ wH β₀ Q hQ)

end Concurrent

/-! ## §3 — the CANARY: the floor at another adversary does not close the bound. -/

/-- **(CANARY.)** The binding does NOT follow from the keyed floor applied at some OTHER adversary
`B`: `keyedRom_hard … B hB` bounds a DIFFERENT ensemble, and only the carrier reduction connects the
extracted finder to the opening game. -/
example (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (crRomGame (Fin 3) (Fin 5)))
    (B : Adversary (keyedRomGame (crRomFamily (Fin 3) (Fin 5))))
    (hB : KeyedRomEff (crRomFamily (Fin 3) (Fin 5)) Q B) : True := by
  fail_if_success
    (have : Negl (gameAdv (crRomGame (Fin 3) (Fin 5)) A) :=
      keyedRom_hard (crRomFamily (Fin 3) (Fin 5)) Q hQ
        (crRomFamily_card_R (Fin 3) (Fin 5)) B hB)
  trivial

/-- **(TOOTH — the binding FIRES on a concrete instance.)** Three signers, five reveals: the
`0`-query hardcoded equivocator is admitted, wins with positive probability, and its advantage is
negligible — the whole spine elaborates end-to-end at a closed instance. -/
theorem crRom_fires :
    (∃ A, RomCarrierEff (crRomFamily (Fin 3) (Fin 5)) (crRomCarrier (Fin 3) (Fin 5))
        (fun l => l + 1) A ∧ ∀ l, 0 < gameAdv (crRomGame (Fin 3) (Fin 5)) A l)
    ∧ Negl (gameAdv (crRomGame (Fin 3) (Fin 5))
        (romCarrierAdv _ _ (constTripleComp _ (crRomCarrier (Fin 3) (Fin 5))
          (fun _ => ((0 : Fin 3), ())) (fun _ => (0 : Fin 5)) (fun _ => (1 : Fin 5))))) := by
  refine ⟨crRom_class_inhabited_pos (Fin 3) (Fin 5) (fun l => l + 1) 0
    (w := (0 : Fin 5)) (w' := (1 : Fin 5)) (by decide), ?_⟩
  refine crRom_constAnswer_defanged (Fin 3) (Fin 5) (fun l => l + 1) ⟨2, 6, ?_⟩ _ _ _
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  crRomFamily_card_R,
  crRom_equivocation_is_break,
  commitReveal_binds_rom,
  crRom_class_inhabited_pos,
  crRom_constAnswer_defanged,
  crRom_nonNegl_forger_excluded,
  cfEquivRom_hard,
  hermine_concurrent_forgery_rom,
  crRom_fires
]

end Dregg2.Crypto.HermineRomBinding
