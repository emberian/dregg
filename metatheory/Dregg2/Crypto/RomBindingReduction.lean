/-
# `Dregg2.Crypto.RomBindingReduction` — a deployed commitment binding, RE-GROUNDED on the keyed,
query-counted floor, with the forger an ORACLE PROGRAM and the floor PROVED (not assumed, not false).

## What this re-grounds, and why the raw-function spine could not be re-grounded in place

`SpongeCarrierReduction.carrier_binds_from_polyTime` and
`Market.WideCommitBoundary.stateCommit_binds_from_polyTime` are the deployed commitment bindings. They
are SECURITY REDUCTIONS — a forger becomes a hash-collision finder — but they discharge efficiency at
`Eff := CostAdversary.IsPolyTime`, and

    HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))

is **FALSE** at deployed parameters (`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear`):
`IsPolyTime` prices answer SIZE, so a `Classical.choice` `.pure`-leaf answering with a short collision
is in the class and wins. Those reductions are therefore VACUOUS at the discharge site.

⚑ **The floor cannot be repaired by choosing a better `Eff` over the SAME game.** In
`hashGame (spongeFamily D)` the hash is a FIXED, KNOWN function and only the tag is sampled. Against a
fixed known function, an adversary that may query it — even a QUERY-BOUNDED one — brute-forces a
collision (the function is public), so NO query-counted `Eff` makes that floor both true and
non-vacuous. Collision resistance of a FIXED function is not a Lean theorem; it is a conjecture. The
floor must move to a SAMPLED oracle (the random-oracle model of the deployed sponge), where the birthday
bound is a THEOREM and query-counting has teeth. That is `KeyedRomFloor`, and it is what this module
reduces to.

## The re-grounded shape (the pattern every `_binds_from_polyTime` should become)

  * **The forger is an ORACLE PROGRAM.** `RomCarrierComp` — a per-parameter `OracleComp` over the
    tag-separated domain, `Q`-query-bounded (`RomCarrierEff`). It learns the sponge only by querying it,
    exactly as the deployed prover does; the key/oracle is sampled AFTER the program is fixed.
  * **The extractor is a POST-MAP of the program** (`OracleComp.mapOut`), so a query-bounded forger
    yields a query-bounded collision finder — `carrierFinder_in_romEff`, the honest successor to the
    `poly_time` discharge, and it PRESERVES the query bound rather than pricing answer size.
  * **The floor is PROVED.** `romCarrier_binds` closes the binding from `KeyedRomFloor.keyedRom_hard`
    (the birthday bound), with NO false hypothesis and NO cost model.
  * **The counterexample dies.** `romCarrier_choiceForger_excluded`: a forger whose advantage is not
    negligible is OUTSIDE the class — the direct analogue of `shortCollAdv`'s exclusion, now at the
    binding layer.

## What a full A1 unification (`docs/reference/ADOPT-ARKLIB-VCVIO-IDEAS.md`) still needs

This closes the carrier PATTERN. Re-pointing each deployed `_binds_from_polyTime` at it is the
remaining mechanical work: the raw-function forger `Adversary (carrierBreakGame …)` /
`Adversary (stateCommitBreakGame …)` must be RESTATED as a `RomCarrierComp`-style oracle program, and
`carrierBreakToFinder` / `stateBreakToWireBreak → wireBreakToFinder` composed with `mapOut`. The
reduction bodies transfer unchanged; only the adversary TYPE moves from a raw function to a query tree.
No new proof of collision resistance is created or needed — the birthday floor supplies it.

⚑ The CHAINED case is NOT mechanical, and is now CLOSED: for `wireCommitR8` the collision sits at an
interior chain step that depends on the oracle's answers, so the extractor cannot be a `mapOut` — it
must RE-WALK both chains, paying queries. `RomChainedReduction` supplies that (`OracleComp.bind`, the
chain as an oracle program, the walking extractor, `romChained_binds`), and
`Market.WideCommitBoundary` §P/§Q/§S lands it on the deployed state-commit schedule — the vacuous
`stateCommit_binds_from_polyTime` is DELETED there, with its floor hypothesis PROVED false
(`stateCommit_floor_polyTime_false_babyBear`).

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Crypto.KeyedRomFloor
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.RomBindingReduction

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary Hard gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor (RomFamily romCollisionGame RomComp romAdv RomEff romCollision_hard)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily keyedRomGame KeyedRomEff keyedRom_hard)

set_option autoImplicit false

/-! ## §1 — post-mapping a query tree's OUTPUT: the extractor, at the oracle level. -/

/-- **MAP THE RETURN VALUE of an oracle program**, leaving its query structure untouched. This is the
extractor as an operation on programs: apply `f` at every `pure` leaf, keep every `query`. -/
def OracleComp.mapOut {D R A B : Type} (f : A → B) : OracleComp D R A → OracleComp D R B
  | .pure a => .pure (f a)
  | .query d k => .query d (fun r => OracleComp.mapOut f (k r))

/-- **Post-mapping commutes with evaluation** — running the mapped program is `f` of running the
original. So the extractor's behaviour is `f` applied to the forger's output, oracle by oracle. -/
theorem OracleComp.mapOut_eval {D R A B : Type} (f : A → B) (M : OracleComp D R A) (H : D → R) :
    (OracleComp.mapOut f M).eval H = f (M.eval H) := by
  induction M with
  | pure a => rfl
  | query d k ih =>
      show (OracleComp.mapOut f (k (H d))).eval H = f ((k (H d)).eval H)
      exact ih (H d)

/-- **Post-mapping preserves the query budget** — it adds no queries, so a `Q`-query forger yields a
`Q`-query collision finder. This is why the reduction preserves the query-counted class. -/
theorem OracleComp.mapOut_queryBounded {D R A B : Type} (f : A → B) {Q : ℕ}
    {M : OracleComp D R A} (h : QueryBounded Q M) : QueryBounded Q (OracleComp.mapOut f M) := by
  induction h with
  | pure n a => exact QueryBounded.pure n (f a)
  | query n d k _ ih => exact QueryBounded.query n d _ (fun r => ih r)

/-! ## §2 — a deployed commitment carrier, with an oracle-program forger. -/

/-- **A DEPLOYED COMMITMENT CARRIER over a keyed random oracle.** The commitment is `H (encode c v)`
for a structural encoding into the tag-separated domain that is injective in the payload. This is the
`SpongeCarrier.ofFlatEncoding` shape — the commonest deployed 1-felt commitment — moved to the oracle
model: the only per-site content is `encode` and its injectivity, and the reduction supplies the rest. -/
structure RomCarrier (F : KeyedRomFamily) where
  /-- The shared context both claims agree on (the deployment's fixed opening data). -/
  Ctx : ℕ → Type
  /-- The payload the commitment is supposed to bind. -/
  Val : ℕ → Type
  /-- Decidable equality on payloads (the win event compares two of them). -/
  valDec : ∀ l, DecidableEq (Val l)
  /-- The structural encoding of a payload-in-context into the tag-separated oracle domain. -/
  encode : ∀ l, Ctx l → Val l → F.toRomFamily.D l
  /-- **THE ENCODING IS INJECTIVE IN THE PAYLOAD** — a layout fact the deployment genuinely satisfies,
  never a claim about the hash. Two distinct payloads in one context encode to two distinct messages. -/
  encode_inj : ∀ l (c : Ctx l) (a b : Val l), encode l c a = encode l c b → a = b

/-- **THE CARRIER COMMITMENT** — one oracle query at the encoded message. -/
def RomCarrier.enc {F : KeyedRomFamily} (C : RomCarrier F) (l : ℕ)
    (H : (keyedRomGame F).Inst l) (c : C.Ctx l) (v : C.Val l) : F.toRomFamily.R l :=
  H (C.encode l c v)

/-- **THE CARRIER FORGERY GAME.** The instance is the sampled keyed oracle; the adversary wins iff it
outputs a context and two DISTINCT payloads carrying the SAME commitment — it equivocates the deployed
commitment. The break is IN the win relation, and it is checked against the SAMPLED oracle. -/
def romCarrierGame (F : KeyedRomFamily) (C : RomCarrier F) : Game where
  Inst := fun l => F.toRomFamily.D l → F.toRomFamily.R l
  Ans := fun l => C.Ctx l × C.Val l × C.Val l
  instFin := fun l => (romCollisionGame F.toRomFamily).instFin l
  instNe := fun l => (romCollisionGame F.toRomFamily).instNe l
  wins := fun l H p => p.2.1 ≠ p.2.2 ∧ C.enc l H p.1 p.2.1 = C.enc l H p.1 p.2.2
  winsDec := fun l H p => by letI := C.valDec l; letI := (F.toRomFamily).rDec l; infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation is a genuine equivocation of the deployed
commitment at the sampled oracle. -/
theorem romCarrierGame_wins_iff (F : KeyedRomFamily) (C : RomCarrier F) (l : ℕ)
    (H : (romCarrierGame F C).Inst l) (p : C.Ctx l × C.Val l × C.Val l) :
    (romCarrierGame F C).wins l H p ↔
      (p.2.1 ≠ p.2.2 ∧ C.enc l H p.1 p.2.1 = C.enc l H p.1 p.2.2) :=
  Iff.rfl

/-- **A CARRIER FORGER, AS AN ORACLE PROGRAM** — one query tree per parameter, over the tag-separated
domain, returning a context and two payloads. Unlike the raw-function forger of the deployed spine, it
learns the sponge only by querying it. -/
abbrev RomCarrierComp (F : KeyedRomFamily) (C : RomCarrier F) : Type :=
  ∀ l, OracleComp (F.toRomFamily.D l) (F.toRomFamily.R l) (C.Ctx l × C.Val l × C.Val l)

/-- The ordinary adversary a carrier query tree induces: run the tree against the oracle. -/
def romCarrierAdv (F : KeyedRomFamily) (C : RomCarrier F) (M : RomCarrierComp F C) :
    Adversary (romCarrierGame F C) where
  run := fun l H => (M l).eval H

/-- **⚑ THE QUERY-BOUNDED CARRIER CLASS — the fixed `Eff` at the binding layer.** A carrier forger is
efficient iff it factors through a `Q`-query tree. This is the honest successor to the `IsPolyTime`
discharge: it bounds QUERIES, and the oracle is sampled after the tree is fixed. -/
def RomCarrierEff (F : KeyedRomFamily) (C : RomCarrier F) (Q : ℕ → ℕ) :
    Adversary (romCarrierGame F C) → Prop := fun A =>
  ∃ M : RomCarrierComp F C, (∀ l, QueryBounded (Q l) (M l)) ∧
    ∀ l (H : (romCarrierGame F C).Inst l), A.run l H = (M l).eval H

/-! ## §3 — the reduction: the extractor as a MAP OF ADVERSARIES, at the oracle level. -/

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A commitment equivocator becomes a collision finder by
returning the two encoded messages. This is the reduction; `encode_inj` is why it works. -/
def carrierFinder (F : KeyedRomFamily) (C : RomCarrier F)
    (A : Adversary (romCarrierGame F C)) : Adversary (keyedRomGame F) where
  run := fun l H => let p := A.run l H; (C.encode l p.1 p.2.1, C.encode l p.1 p.2.2)

/-- **⚑ WIN-PRESERVATION.** Every oracle on which the equivocator wins, the extracted finder wins the
collision game of the SAMPLED oracle: the two encoded messages are distinct (`encode_inj` on the
distinct payloads) and share a digest (the equal commitments). -/
theorem carrier_wins_imp (F : KeyedRomFamily) (C : RomCarrier F)
    (A : Adversary (romCarrierGame F C)) (l : ℕ) (H : (romCarrierGame F C).Inst l)
    (hwin : (romCarrierGame F C).wins l H (A.run l H)) :
    (keyedRomGame F).wins l H ((carrierFinder F C A).run l H) := by
  obtain ⟨hne, heq⟩ := hwin
  refine ⟨fun hc => hne (C.encode_inj l (A.run l H).1 (A.run l H).2.1 (A.run l H).2.2 hc), ?_⟩
  exact heq

/-- **⚑ THE ADVANTAGE INEQUALITY — UNCONDITIONAL, over ALL adversaries.** The equivocator's advantage
is at most the extracted collision finder's, at every parameter. The adversary class does NOT appear;
it enters only when the floor is applied. -/
theorem carrier_adv_le (F : KeyedRomFamily) (C : RomCarrier F)
    (A : Adversary (romCarrierGame F C)) (l : ℕ) :
    gameAdv (romCarrierGame F C) A l ≤ gameAdv (keyedRomGame F) (carrierFinder F C A) l := by
  refine @winProb_le_of_imp _ ((romCarrierGame F C).instFin l) _ _ (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  exact (Adversary.hit_eq_true (carrierFinder F C A) l H).mpr (carrier_wins_imp F C A l H hH)

/-- **⚑ THE EXTRACTED FINDER IS QUERY-BOUNDED — the efficiency discharge, PRESERVING THE QUERY BOUND.**
A `Q`-query carrier forger yields a `Q`-query collision finder, because the extractor is a `mapOut`
post-composition (`OracleComp.mapOut_queryBounded`), which adds no queries. This is what replaces the
`poly_time` answer-size discharge: the finder is admitted by `RomEff` because it makes few CALLS, not
because it writes a short answer. -/
theorem carrierFinder_in_romEff (F : KeyedRomFamily) (C : RomCarrier F) (Q : ℕ → ℕ)
    (A : Adversary (romCarrierGame F C)) (hA : RomCarrierEff F C Q A) :
    RomEff F.toRomFamily Q (carrierFinder F C A) := by
  obtain ⟨M, hMQ, hrun⟩ := hA
  refine ⟨fun l => OracleComp.mapOut
      (fun p => (C.encode l p.1 p.2.1, C.encode l p.1 p.2.2)) (M l), ?_, ?_⟩
  · exact fun l => OracleComp.mapOut_queryBounded _ (hMQ l)
  · intro l H
    show (let p := A.run l H; (C.encode l p.1 p.2.1, C.encode l p.1 p.2.2))
      = (OracleComp.mapOut (fun p => (C.encode l p.1 p.2.1, C.encode l p.1 p.2.2)) (M l)).eval H
    exact (congrArg (fun p => (C.encode l p.1 p.2.1, C.encode l p.1 p.2.2)) (hrun l H)).trans
      (OracleComp.mapOut_eval (fun p => (C.encode l p.1 p.2.1, C.encode l p.1 p.2.2)) (M l) H).symm

/-- **⚑⚑ THE RE-GROUNDED BINDING — from the KEYED, QUERY-COUNTED floor, WHICH IS PROVED.**

A carrier forger in the query-bounded class has NEGLIGIBLE advantage: at a `λ`-bit digest and a
polynomial query budget, the deployed commitment binds its payload except with negligible probability.

This is what replaces `carrier_binds_from_polyTime` / `stateCommit_binds_from_polyTime`. The difference
is the whole point: the floor here is `keyedRom_hard`, a THEOREM (the birthday bound), whereas the
`IsPolyTime` floor those carry is FALSE at deployed parameters. Efficiency is discharged by
`carrierFinder_in_romEff` (query-bound preservation), not by pricing answer size. -/
theorem romCarrier_binds (F : KeyedRomFamily) (C : RomCarrier F) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (A : Adversary (romCarrierGame F C)) (hA : RomCarrierEff F C Q A) :
    Negl (gameAdv (romCarrierGame F C) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (romCarrierGame F C) A l).1)
    (carrier_adv_le F C A)
    (keyedRom_hard F Q hQ hw (carrierFinder F C A) (carrierFinder_in_romEff F C Q A hA))

/-! ## §4 — ⚑ THE COUNTEREXAMPLE DIES AT THE BINDING LAYER. -/

/-- **⚑ A NON-NEGLIGIBLE FORGER IS EXCLUDED FROM THE CLASS.** The `shortCollAdv` analogue at the
binding layer: a forger that equivocates the commitment with non-negligible probability is NOT in the
query-bounded class — if it were, `romCarrier_binds` would make its advantage negligible. So the
strategy that refutes the `IsPolyTime`-discharged binding cannot produce a member of the fixed class. -/
theorem romCarrier_choiceForger_excluded (F : KeyedRomFamily) (C : RomCarrier F) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (A : Adversary (romCarrierGame F C))
    (hnn : ¬ Negl (gameAdv (romCarrierGame F C) A)) :
    ¬ RomCarrierEff F C Q A :=
  fun hA => hnn (romCarrier_binds F C Q hQ hw A hA)

/-! ## §5 — the interface is INHABITED (the spine is witnessed non-vacuous). -/

/-- **A CONCRETE CARRIER** — the identity commitment `enc H _ v = H v` on the tag-separated domain: an
equivocation IS a collision, so the encoding is the identity and injective on the nose. Small, but it
proves the `RomCarrier` interface is inhabited — a structure nothing can satisfy is the failure mode
this whole re-grounding retires. -/
def idRomCarrier (F : KeyedRomFamily) : RomCarrier F where
  Ctx := fun _ => Unit
  Val := fun l => F.toRomFamily.D l
  valDec := fun l => (F.toRomFamily).dDec l
  encode := fun _ _ v => v
  encode_inj := fun _ _ _ _ h => h

/-- The re-grounded binding FIRES on the identity carrier: the interface is inhabited and the reduction
elaborates end-to-end on the PROVED floor. -/
theorem idRomCarrier_binds (F : KeyedRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (A : Adversary (romCarrierGame F (idRomCarrier F))) (hA : RomCarrierEff F (idRomCarrier F) Q A) :
    Negl (gameAdv (romCarrierGame F (idRomCarrier F)) A) :=
  romCarrier_binds F (idRomCarrier F) Q hQ hw A hA

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  OracleComp.mapOut_eval,
  OracleComp.mapOut_queryBounded,
  romCarrierGame_wins_iff,
  carrier_wins_imp,
  carrier_adv_le,
  carrierFinder_in_romEff,
  romCarrier_binds,
  romCarrier_choiceForger_excluded,
  idRomCarrier_binds
]

end Dregg2.Crypto.RomBindingReduction
