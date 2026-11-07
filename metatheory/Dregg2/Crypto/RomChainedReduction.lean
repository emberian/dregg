/-
# `Dregg2.Crypto.RomChainedReduction` — the CHAINED commitment as an ORACLE COMPUTATION, and its
binding RE-GROUNDED on the keyed, query-counted floor.

## Why the flat carrier does not cover the deployed state commit

`RomBindingReduction.RomCarrier` re-grounds every commitment of the shape `H (encode c v)` — ONE
oracle call per commitment. The deployed wide state anchor is not that shape:
`Market.WideCommitBoundary.commit8` is `wireCommitR8`, a CHAINED absorption — a 4-limb head is
absorbed, then 3-limb chunks EACH FEEDING THE PREVIOUS DIGEST BACK INTO THE NEXT CALL, then the
receipt root last. A forger against it does not equivocate one query; it equivocates a CHAIN of
queries, and the collision its forgery yields sits at some INTERIOR step whose position depends on
the oracle's own answers. So the extractor cannot be a post-map of the forger's output
(`RomBindingReduction.OracleComp.mapOut` adds no queries and sees no digests): to FIND the colliding
step it must WALK both chains, querying the oracle as it goes — and those queries must be PAID FOR
in the class the floor quantifies over.

## What this file adds (the three missing objects, in the model where the floor is PROVED)

  * **§1 THE CHAIN AS AN ORACLE PROGRAM.** `chainComp enc acc bs` — one `query` node per absorption
    step, the previous ANSWER threaded into the next query point. `chainComp_eval` proves its run
    against any oracle is the fixed-function fold `chainEval`, and `chainComp_queryBounded` prices
    it at exactly one query per block. `Market.WideCommitBoundary.wireCommitComp` instantiates it at
    the DEPLOYED `wireCommitR8` schedule and proves `eval permW = wireCommitR8 permW l ir` — the
    deployed chained commitment IS this program, run at the deployed permutation.
  * **§2 THE CHAINED CARRIER AND ITS FORGERY GAME.** `RomChainedCarrier` — per-site content is the
    head/step encodings into the tag-separated domain and their injectivity: LAYOUT facts a
    deployment genuinely satisfies, never a claim about the hash. The forger (`RomChainedComp`,
    class `RomChainedEff`) is an oracle program fixed BEFORE the oracle is sampled.
  * **§3 THE EXTRACTOR AS AN ORACLE PROGRAM WITH A PAID BUDGET.** `breakFinderComp` re-walks both
    chains two queries per step and returns the first colliding query pair; `OracleComp.bind`
    sequences it after the forger, and `chainedFinder_in_romEff` prices the composed finder at
    `Q + 2·len + 2` queries. The honest successor to `mapOut` for a chained site: the extractor's
    own queries are COUNTED, not free.

`romChained_binds` (§4) closes the binding from `KeyedRomFloor.keyedRom_hard` — the birthday bound,
a THEOREM — with no cost model and no false hypothesis. `romChained_choiceForger_excluded` kills the
`Classical.choice` collision-answerer at this layer: a chained forger whose advantage is not
negligible is OUTSIDE the query-bounded class, because inside it the binding applies.

## Non-vacuity (§5)

The class is inhabited (`fixedChainedForger_in_eff`, a 0-query member) and the game is genuinely
winnable (`romChainedGame_win_at_const`: at a constant oracle EVERY distinct payload pair
equivocates — the chain forgets its input once the digests agree), so the binding is a statement
about a non-empty event over a non-empty class. The deployed-shape instantiation — and the labelled
MODELLING step it requires (`hw` forces a λ-growing digest space; the deployed BabyBear felt is
fixed 31-bit) — lives beside the object it re-grounds, in `Market.WideCommitBoundary` §S.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Crypto.RomBindingReduction
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.RomChainedReduction

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary Hard gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor (RomFamily romCollisionGame RomComp romAdv RomEff)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily keyedRomGame KeyedRomEff keyedRom_hard)

set_option autoImplicit false

/-! ## §0 — sequential composition of oracle programs, and its budget law.

The extractor for a chained site must RUN the forger and THEN keep querying (the chain walk). That
is `bind` — absent from `RomOracle` because the flat reduction only needed `mapOut`. Its two laws
are exactly the two the reduction consumes: running the composition is running the pieces
(`bind_eval`), and budgets ADD (`bind_queryBounded`). -/

/-- **RUN ONE ORACLE PROGRAM, THEN ANOTHER that depends on its output** — graft `f a` onto every
`pure a` leaf, keeping every `query` node.

(⚠ Like `RomBindingReduction.OracleComp.mapOut`, this is declared INSIDE this namespace: its full
name is `Dregg2.Crypto.RomChainedReduction.OracleComp.bind`, and dot-notation `M.bind` will NOT
resolve to it. Open this namespace or fully qualify.) -/
def OracleComp.bind {D R A B : Type} :
    OracleComp D R A → (A → OracleComp D R B) → OracleComp D R B
  | .pure a, f => f a
  | .query d k, f => .query d (fun r => OracleComp.bind (k r) f)

/-- Running the composition is running the pieces: the second program starts from the first one's
output, against the same oracle. -/
theorem OracleComp.bind_eval {D R A B : Type} (M : OracleComp D R A)
    (f : A → OracleComp D R B) (H : D → R) :
    (OracleComp.bind M f).eval H = (f (M.eval H)).eval H := by
  induction M with
  | pure a => rfl
  | query d k ih =>
      show (OracleComp.bind (k (H d)) f).eval H = (f ((k (H d)).eval H)).eval H
      exact ih (H d)

/-- **BUDGETS ADD under sequencing.** A `QM`-query program followed by a `QF`-query continuation is
a `(QM + QF)`-query program — every path interleaves at most both budgets. This is what lets the
chain-walking extractor's queries be PAID rather than smuggled. -/
theorem OracleComp.bind_queryBounded {D R A B : Type} {QM QF : ℕ}
    {M : OracleComp D R A} {f : A → OracleComp D R B}
    (hM : QueryBounded QM M) (hf : ∀ a, QueryBounded QF (f a)) :
    QueryBounded (QM + QF) (OracleComp.bind M f) := by
  induction hM with
  | pure n a => exact (hf a).mono (Nat.le_add_left QF n)
  | query n d k hk ih =>
      have h : QueryBounded (n + QF + 1)
          (OracleComp.query d (fun r => OracleComp.bind (k r) f)) :=
        QueryBounded.query _ d _ (fun r => ih r)
      exact h.mono (by omega)

/-! ## §1 — THE CHAINED ABSORPTION, AS AN ORACLE COMPUTATION.

The deployed shape (`wireCommitR8` / `chainFrom8`): an accumulator digest, updated one block at a
time by hashing `enc acc b`. Generic in the domain/range/block types so the SAME definition serves
the deployed `List ℤ` fold (where `enc acc b = acc ++ b` and the "oracle" is the fixed `permW`) and
the finite tag-separated oracle domain of the keyed floor. -/

/-- The FIXED-FUNCTION chained absorption: fold the blocks through `H ∘ enc`. At
`enc acc b = acc ++ b`, `H = permW` this IS the deployed `chainFrom8`
(`Market.WideCommitBoundary.chainEval_append_eq_chainFrom8`). -/
def chainEval {D R Blk : Type} (H : D → R) (enc : R → Blk → D) : R → List Blk → R
  | acc, [] => acc
  | acc, b :: bs => chainEval H enc (H (enc acc b)) bs

/-- **⚑ THE CHAIN, AS AN ORACLE PROGRAM** — one `query` node per absorption step, each query point
built from the PREVIOUS ANSWER. This is the object the re-pointing campaign named: the chained
state commit is not a fixed function of its input, it is a PROGRAM that learns each intermediate
digest only by asking the oracle. -/
def chainComp {D R Blk : Type} (enc : R → Blk → D) : R → List Blk → OracleComp D R R
  | acc, [] => .pure acc
  | acc, b :: bs => .query (enc acc b) (fun r => chainComp enc r bs)

/-- **THE MODEL IS FAITHFUL**: running the chain program against any oracle is the fixed-function
fold of that oracle. Each absorption step became a query; nothing else changed. -/
theorem chainComp_eval {D R Blk : Type} (enc : R → Blk → D) (H : D → R) :
    ∀ (bs : List Blk) (acc : R), (chainComp enc acc bs).eval H = chainEval H enc acc bs
  | [], _ => rfl
  | b :: bs, acc => chainComp_eval enc H bs (H (enc acc b))

/-- **THE CHAIN'S BUDGET IS ITS LENGTH** — one query per absorbed block, exactly. -/
theorem chainComp_queryBounded {D R Blk : Type} (enc : R → Blk → D) :
    ∀ (bs : List Blk) (acc : R), QueryBounded bs.length (chainComp enc acc bs)
  | [], acc => QueryBounded.pure 0 acc
  | _ :: bs, _ => QueryBounded.query _ _ _ (fun r => chainComp_queryBounded enc bs r)

/-- A chain started at a constant oracle's value stays there: `chainEval (const r₀)` from `r₀` is
`r₀`, whatever the blocks. The non-vacuity witness below rides on this. -/
theorem chainEval_const {D R Blk : Type} (enc : R → Blk → D) (r₀ : R) :
    ∀ bs : List Blk, chainEval (fun _ => r₀) enc r₀ bs = r₀
  | [] => rfl
  | _ :: bs => chainEval_const enc r₀ bs

/-! ## §2 — the chained carrier, its commitment program, and its forgery game. -/

/-- **A DEPLOYED CHAINED COMMITMENT CARRIER over a keyed random oracle.** The commitment is the
chained fold: absorb the head (`encHd`), then `len` blocks, each step re-absorbing the previous
digest (`encStep`). The per-site content is the two structural encodings into the tag-separated
domain and their injectivity — layout facts the deployment genuinely satisfies (fixed widths make
`acc ++ c` injective in the pair), NEVER a claim about the hash. The chain LENGTH is pinned by the
carrier (`len`), as deployed: the wide state anchor absorbs a fixed 184-limb payload schedule. -/
structure RomChainedCarrier (F : KeyedRomFamily) where
  /-- The shared context both claims agree on (the deployment's fixed opening data — e.g. the
  domain-separation tag choice). -/
  Ctx : ℕ → Type
  /-- The head block, absorbed first (deployed: the 4-limb `take 4` of the payload). -/
  Hd : ℕ → Type
  /-- One chained block (deployed: a 3-limb `chunk31` chunk, or the final iroot block). -/
  Blk : ℕ → Type
  /-- The deployed chain length — how many chained absorption steps follow the head. -/
  len : ℕ → ℕ
  /-- Decidable equality on heads (the win event compares payloads). -/
  hdDec : ∀ l, DecidableEq (Hd l)
  /-- Decidable equality on blocks. -/
  blkDec : ∀ l, DecidableEq (Blk l)
  /-- The head encoding into the tag-separated oracle domain. -/
  encHd : ∀ l, Ctx l → Hd l → F.toRomFamily.D l
  /-- The step encoding: previous digest and next block, into the oracle domain (deployed:
  `acc ++ c` at fixed widths 8 and 3). -/
  encStep : ∀ l, Ctx l → F.toRomFamily.R l → Blk l → F.toRomFamily.D l
  /-- **HEAD INJECTIVITY IN THE PAYLOAD** — a layout fact, not a hash claim. -/
  encHd_inj : ∀ l (c : Ctx l) (a b : Hd l), encHd l c a = encHd l c b → a = b
  /-- **STEP INJECTIVITY IN THE (digest, block) PAIR** — the deployed fixed-width concatenation
  satisfies this on the nose. -/
  encStep_inj : ∀ l (c : Ctx l) (r : F.toRomFamily.R l) (b : Blk l)
      (r' : F.toRomFamily.R l) (b' : Blk l),
      encStep l c r b = encStep l c r' b' → r = r' ∧ b = b'

/-- A chained payload: a head and exactly `len` blocks (the deployed fixed schedule). -/
abbrev RomChainedCarrier.Val {F : KeyedRomFamily} (C : RomChainedCarrier F) (l : ℕ) : Type :=
  C.Hd l × (Fin (C.len l) → C.Blk l)

/-- The payload's block list, in absorption order. -/
def RomChainedCarrier.blocks {F : KeyedRomFamily} (C : RomChainedCarrier F) {l : ℕ}
    (v : C.Val l) : List (C.Blk l) :=
  List.ofFn v.2

@[simp] theorem RomChainedCarrier.blocks_length {F : KeyedRomFamily} (C : RomChainedCarrier F)
    {l : ℕ} (v : C.Val l) : (C.blocks v).length = C.len l := by
  simp [RomChainedCarrier.blocks]

/-- **THE CHAINED CARRIER COMMITMENT** — head query, then the chain. -/
def RomChainedCarrier.enc {F : KeyedRomFamily} (C : RomChainedCarrier F) (l : ℕ)
    (H : (keyedRomGame F).Inst l) (c : C.Ctx l) (v : C.Val l) : F.toRomFamily.R l :=
  chainEval H (C.encStep l c) (H (C.encHd l c v.1)) (C.blocks v)

/-- **THE HONEST COMMITTER, AS AN ORACLE PROGRAM** — the deployed prover's exact query schedule:
one head query, then one query per block, each carrying the previous digest. -/
def RomChainedCarrier.commitComp {F : KeyedRomFamily} (C : RomChainedCarrier F) (l : ℕ)
    (c : C.Ctx l) (v : C.Val l) :
    OracleComp (F.toRomFamily.D l) (F.toRomFamily.R l) (F.toRomFamily.R l) :=
  .query (C.encHd l c v.1) (fun r => chainComp (C.encStep l c) r (C.blocks v))

/-- The committer program computes the commitment: its run against any oracle is `enc`. -/
theorem RomChainedCarrier.commitComp_eval {F : KeyedRomFamily} (C : RomChainedCarrier F) (l : ℕ)
    (c : C.Ctx l) (v : C.Val l) (H : (keyedRomGame F).Inst l) :
    (C.commitComp l c v).eval H = C.enc l H c v :=
  chainComp_eval (C.encStep l c) H (C.blocks v) (H (C.encHd l c v.1))

/-- The committer pays `len + 1` queries — the deployed absorption count, exactly. -/
theorem RomChainedCarrier.commitComp_queryBounded {F : KeyedRomFamily} (C : RomChainedCarrier F)
    (l : ℕ) (c : C.Ctx l) (v : C.Val l) : QueryBounded (C.len l + 1) (C.commitComp l c v) := by
  refine QueryBounded.query (C.len l) _ _ (fun r => ?_)
  have h := chainComp_queryBounded (C.encStep l c) (C.blocks v) r
  rwa [RomChainedCarrier.blocks_length] at h

/-- **THE CHAINED FORGERY GAME.** The instance is the sampled keyed oracle; the adversary wins iff
it outputs a context and two DISTINCT payloads whose CHAINS collide — it equivocates the deployed
chained commitment against the very oracle that was sampled. -/
def romChainedGame (F : KeyedRomFamily) (C : RomChainedCarrier F) : Game where
  Inst := fun l => F.toRomFamily.D l → F.toRomFamily.R l
  Ans := fun l => C.Ctx l × C.Val l × C.Val l
  instFin := fun l => (romCollisionGame F.toRomFamily).instFin l
  instNe := fun l => (romCollisionGame F.toRomFamily).instNe l
  wins := fun l H p => p.2.1 ≠ p.2.2 ∧ C.enc l H p.1 p.2.1 = C.enc l H p.1 p.2.2
  winsDec := fun l H p => by
    letI := C.hdDec l; letI := C.blkDec l; letI := (F.toRomFamily).rDec l
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation is a genuine equivocation of the chained
commitment at the sampled oracle. -/
theorem romChainedGame_wins_iff (F : KeyedRomFamily) (C : RomChainedCarrier F) (l : ℕ)
    (H : (romChainedGame F C).Inst l) (p : C.Ctx l × C.Val l × C.Val l) :
    (romChainedGame F C).wins l H p ↔
      (p.2.1 ≠ p.2.2 ∧ C.enc l H p.1 p.2.1 = C.enc l H p.1 p.2.2) :=
  Iff.rfl

/-- **A CHAINED FORGER, AS AN ORACLE PROGRAM** — one query tree per parameter, fixed BEFORE the
oracle is sampled. -/
abbrev RomChainedComp (F : KeyedRomFamily) (C : RomChainedCarrier F) : Type :=
  ∀ l, OracleComp (F.toRomFamily.D l) (F.toRomFamily.R l) (C.Ctx l × C.Val l × C.Val l)

/-- The ordinary adversary a chained query tree induces: run the tree against the oracle. -/
def romChainedAdv (F : KeyedRomFamily) (C : RomChainedCarrier F) (M : RomChainedComp F C) :
    Adversary (romChainedGame F C) where
  run := fun l H => (M l).eval H

/-- **⚑ THE QUERY-BOUNDED CHAINED CLASS — the fixed `Eff` at the chained binding layer.** A chained
forger is efficient iff it factors through a `Q`-query tree. Same shape as `RomCarrierEff`; what
changes downstream is that the EXTRACTOR now spends queries too, and pays for them. -/
def RomChainedEff (F : KeyedRomFamily) (C : RomChainedCarrier F) (Q : ℕ → ℕ) :
    Adversary (romChainedGame F C) → Prop := fun A =>
  ∃ M : RomChainedComp F C, (∀ l, QueryBounded (Q l) (M l)) ∧
    ∀ l (H : (romChainedGame F C).Inst l), A.run l H = (M l).eval H

/-! ## §3 — the extractor: a CHAIN WALK that pays its own queries.

Two equal-length chains with equal final digests but different inputs must disagree at some query
point while agreeing on the answer — a genuine collision of the SAMPLED oracle. Which step that is
depends on the oracle, so the extractor re-runs both chains (two queries per step), comparing as it
goes. `chainCollComp` is that walk as an oracle program; `chainCollComp_eval_collides` is its
correctness; `breakFinderComp` adds the head layer. -/

/-- **THE CHAIN WALK, AS AN ORACLE PROGRAM.** Walk both chains in lockstep; at each step query both
points; the first step whose points DIFFER while the answers AGREE is a collision — return it.
`dflt` is returned only on paths where no collision is found (never taken on a winning forgery, as
the spec proves). -/
def chainCollComp {D R Blk : Type} [DecidableEq D] [DecidableEq R]
    (enc : R → Blk → D) (dflt : D × D) :
    R → R → List Blk → List Blk → OracleComp D R (D × D)
  | _, _, [], _ => .pure dflt
  | _, _, _ :: _, [] => .pure dflt
  | acc, acc', b :: bs, b' :: bs' =>
      .query (enc acc b) (fun r =>
        .query (enc acc' b') (fun r' =>
          if enc acc b ≠ enc acc' b' ∧ r = r' then .pure (enc acc b, enc acc' b')
          else chainCollComp enc dflt r r' bs bs'))

/-- **THE WALK PAYS TWO QUERIES PER STEP** — `2 · |bs|`, along every path. -/
theorem chainCollComp_queryBounded {D R Blk : Type} [DecidableEq D] [DecidableEq R]
    (enc : R → Blk → D) (dflt : D × D) :
    ∀ (bs bs' : List Blk) (acc acc' : R),
      QueryBounded (2 * bs.length) (chainCollComp enc dflt acc acc' bs bs') := by
  intro bs
  induction bs with
  | nil => intro bs' acc acc'; exact QueryBounded.pure _ _
  | cons b bs ih =>
      intro bs' acc acc'
      cases bs' with
      | nil => exact QueryBounded.pure _ _
      | cons b' bs' =>
          have h2 : 2 * (b :: bs).length = 2 * bs.length + 1 + 1 := by
            simp [List.length_cons]; ring
          rw [h2]
          refine QueryBounded.query _ _ _ (fun r => ?_)
          refine QueryBounded.query _ _ _ (fun r' => ?_)
          split
          · exact QueryBounded.pure _ _
          · exact ih bs' r r'

/-- **⚑ THE WALK IS CORRECT.** For two equal-length chains with EQUAL folds but DIFFERENT inputs
(different starting digests, or different block lists), the walk's run returns a GENUINE collision
of the oracle: two distinct query points with equal answers. The interior step exists because
`enc`'s injectivity pushes any difference forward until the digests merge — and the merge point IS
the collision. -/
theorem chainCollComp_eval_collides {D R Blk : Type} [DecidableEq D] [DecidableEq R]
    (enc : R → Blk → D)
    (hinj : ∀ (r : R) (b : Blk) (r' : R) (b' : Blk), enc r b = enc r' b' → r = r' ∧ b = b')
    (H : D → R) (dflt : D × D) :
    ∀ (bs bs' : List Blk) (acc acc' : R), bs.length = bs'.length →
      chainEval H enc acc bs = chainEval H enc acc' bs' →
      (acc ≠ acc' ∨ bs ≠ bs') →
      ((chainCollComp enc dflt acc acc' bs bs').eval H).1
          ≠ ((chainCollComp enc dflt acc acc' bs bs').eval H).2
        ∧ H ((chainCollComp enc dflt acc acc' bs bs').eval H).1
          = H ((chainCollComp enc dflt acc acc' bs bs').eval H).2 := by
  intro bs
  induction bs with
  | nil =>
      intro bs' acc acc' hlen heq hne
      have hbs' : bs' = [] := by
        cases bs' with
        | nil => rfl
        | cons _ _ => simp at hlen
      subst hbs'
      rcases hne with h | h
      · exact absurd heq h
      · exact absurd rfl h
  | cons b bs ih =>
      intro bs' acc acc' hlen heq hne
      cases bs' with
      | nil => simp at hlen
      | cons b' bs' =>
          have hred : (chainCollComp enc dflt acc acc' (b :: bs) (b' :: bs')).eval H
              = (if enc acc b ≠ enc acc' b' ∧ H (enc acc b) = H (enc acc' b')
                  then OracleComp.pure (enc acc b, enc acc' b')
                  else chainCollComp enc dflt (H (enc acc b)) (H (enc acc' b')) bs bs').eval H :=
            rfl
          rw [hred]
          by_cases hcoll : enc acc b ≠ enc acc' b' ∧ H (enc acc b) = H (enc acc' b')
          · rw [if_pos hcoll]
            exact ⟨hcoll.1, hcoll.2⟩
          · rw [if_neg hcoll]
            have hcoll' : enc acc b ≠ enc acc' b' → H (enc acc b) ≠ H (enc acc' b') :=
              fun hp hq => hcoll ⟨hp, hq⟩
            have heq' : chainEval H enc (H (enc acc b)) bs
                = chainEval H enc (H (enc acc' b')) bs' := heq
            have hlen' : bs.length = bs'.length := by simpa using hlen
            by_cases henc : enc acc b = enc acc' b'
            · obtain ⟨hacc, hb⟩ := hinj _ _ _ _ henc
              subst hacc
              subst hb
              have hbs : bs ≠ bs' := by
                rcases hne with h | h
                · exact absurd rfl h
                · intro hbb
                  exact h (by rw [hbb])
              exact ih bs' (H (enc acc b)) (H (enc acc b)) hlen'
                (by simpa [henc] using heq') (Or.inr hbs)
            · exact ih bs' (H (enc acc b)) (H (enc acc' b')) hlen' heq'
                (Or.inl (hcoll' henc))

/-- **THE FULL EXTRACTOR PROGRAM** — the head layer (compare the two head queries first), then the
chain walk. Its input is the forger's ANSWER; its queries recompute both chains against the SAME
sampled oracle the forgery was checked against. -/
def breakFinderComp {F : KeyedRomFamily} (C : RomChainedCarrier F) (l : ℕ)
    (p : C.Ctx l × C.Val l × C.Val l) :
    OracleComp (F.toRomFamily.D l) (F.toRomFamily.R l)
      (F.toRomFamily.D l × F.toRomFamily.D l) :=
  letI := (F.toRomFamily).dDec l
  letI := (F.toRomFamily).rDec l
  .query (C.encHd l p.1 p.2.1.1) (fun r =>
    .query (C.encHd l p.1 p.2.2.1) (fun r' =>
      if C.encHd l p.1 p.2.1.1 ≠ C.encHd l p.1 p.2.2.1 ∧ r = r'
      then .pure (C.encHd l p.1 p.2.1.1, C.encHd l p.1 p.2.2.1)
      else chainCollComp (C.encStep l p.1) (C.encHd l p.1 p.2.1.1, C.encHd l p.1 p.2.2.1)
        r r' (C.blocks p.2.1) (C.blocks p.2.2)))

/-- **THE EXTRACTOR'S BUDGET IS `2·len + 2`** — two head queries plus the walk. A constant of the
deployed schedule, proved, not declared. -/
theorem breakFinderComp_queryBounded {F : KeyedRomFamily} (C : RomChainedCarrier F) (l : ℕ)
    (p : C.Ctx l × C.Val l × C.Val l) :
    QueryBounded (2 * C.len l + 2) (breakFinderComp C l p) := by
  letI := (F.toRomFamily).dDec l
  letI := (F.toRomFamily).rDec l
  unfold breakFinderComp
  refine QueryBounded.query (2 * C.len l + 1) _ _ (fun r => ?_)
  refine QueryBounded.query (2 * C.len l) _ _ (fun r' => ?_)
  split
  · exact QueryBounded.pure _ _
  · have h := chainCollComp_queryBounded (C.encStep l p.1)
      (C.encHd l p.1 p.2.1.1, C.encHd l p.1 p.2.2.1) (C.blocks p.2.1) (C.blocks p.2.2) r r'
    rwa [RomChainedCarrier.blocks_length] at h

/-- **⚑ THE EXTRACTOR IS CORRECT ON EVERY WINNING FORGERY**: whenever the forger's answer wins the
chained game at `H`, the extractor's run at `H` is a genuine collision of `H`. Head-layer case
split: if the head digests already collide at distinct points, that pair is the answer; otherwise
the heads either coincide (so the payload difference lives in the blocks — `encHd_inj`) or their
digests differ (so the chains start apart), and the walk finds the merge. -/
theorem breakFinderComp_eval_collides {F : KeyedRomFamily} (C : RomChainedCarrier F) (l : ℕ)
    (H : (romChainedGame F C).Inst l) (p : C.Ctx l × C.Val l × C.Val l)
    (hwin : (romChainedGame F C).wins l H p) :
    ((breakFinderComp C l p).eval H).1 ≠ ((breakFinderComp C l p).eval H).2
      ∧ H ((breakFinderComp C l p).eval H).1 = H ((breakFinderComp C l p).eval H).2 := by
  obtain ⟨c, v, v'⟩ := p
  obtain ⟨hne, heq⟩ := hwin
  letI := (F.toRomFamily).dDec l
  letI := (F.toRomFamily).rDec l
  have hred : (breakFinderComp C l (c, v, v')).eval H
      = (if C.encHd l c v.1 ≠ C.encHd l c v'.1 ∧ H (C.encHd l c v.1) = H (C.encHd l c v'.1)
          then OracleComp.pure (C.encHd l c v.1, C.encHd l c v'.1)
          else chainCollComp (C.encStep l c) (C.encHd l c v.1, C.encHd l c v'.1)
            (H (C.encHd l c v.1)) (H (C.encHd l c v'.1))
            (C.blocks v) (C.blocks v')).eval H := rfl
  rw [hred]
  by_cases hhd : C.encHd l c v.1 ≠ C.encHd l c v'.1
      ∧ H (C.encHd l c v.1) = H (C.encHd l c v'.1)
  · rw [if_pos hhd]
    exact ⟨hhd.1, hhd.2⟩
  · rw [if_neg hhd]
    have hhd' : C.encHd l c v.1 ≠ C.encHd l c v'.1
        → H (C.encHd l c v.1) ≠ H (C.encHd l c v'.1) :=
      fun hp hq => hhd ⟨hp, hq⟩
    have hlen : (C.blocks v).length = (C.blocks v').length := by simp
    by_cases henc : C.encHd l c v.1 = C.encHd l c v'.1
    · have hv1 : v.1 = v'.1 := C.encHd_inj l c _ _ henc
      have hblocks : C.blocks v ≠ C.blocks v' := by
        intro hb
        apply hne
        have hfn : v.2 = v'.2 := List.ofFn_inj.mp hb
        exact Prod.ext hv1 hfn
      exact chainCollComp_eval_collides (C.encStep l c) (C.encStep_inj l c) H _
        (C.blocks v) (C.blocks v') _ _ hlen heq (Or.inr hblocks)
    · exact chainCollComp_eval_collides (C.encStep l c) (C.encStep_inj l c) H _
        (C.blocks v) (C.blocks v') _ _ hlen heq (Or.inl (hhd' henc))

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A chained equivocator becomes a collision finder of
the sampled keyed oracle: run the forger, then run the walk — against the same instance. -/
def chainedFinder (F : KeyedRomFamily) (C : RomChainedCarrier F)
    (A : Adversary (romChainedGame F C)) : Adversary (keyedRomGame F) where
  run := fun l H => (breakFinderComp C l (A.run l H)).eval H

/-- **⚑ WIN-PRESERVATION.** Every oracle on which the chained forger wins, the extracted finder
wins the keyed collision game — the walk's correctness, at the game level. -/
theorem chained_wins_imp (F : KeyedRomFamily) (C : RomChainedCarrier F)
    (A : Adversary (romChainedGame F C)) (l : ℕ) (H : (romChainedGame F C).Inst l)
    (hwin : (romChainedGame F C).wins l H (A.run l H)) :
    (keyedRomGame F).wins l H ((chainedFinder F C A).run l H) :=
  breakFinderComp_eval_collides C l H (A.run l H) hwin

/-- **THE ADVANTAGE INEQUALITY — UNCONDITIONAL, over ALL adversaries.** The chained forger's
advantage is at most the extracted finder's, at every parameter. The class enters only at the
floor. -/
theorem chained_adv_le (F : KeyedRomFamily) (C : RomChainedCarrier F)
    (A : Adversary (romChainedGame F C)) (l : ℕ) :
    gameAdv (romChainedGame F C) A l ≤ gameAdv (keyedRomGame F) (chainedFinder F C A) l := by
  refine @winProb_le_of_imp _ ((romChainedGame F C).instFin l) _ _ (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  exact (Adversary.hit_eq_true _ _ _).mpr (chained_wins_imp F C A l H hH)

/-- **⚑ THE EXTRACTED FINDER IS QUERY-BOUNDED, WITH THE WALK'S QUERIES PAID.** A `Q`-query chained
forger yields a `(Q + 2·len + 2)`-query collision finder: the forger's own tree (`bind`) plus the
extractor's re-walk. This is the honest successor to the `poly_time` answer-size discharge AND to
the flat `mapOut` discharge: the reduction's cost is counted in the SAME currency the floor
quantifies over. -/
theorem chainedFinder_in_romEff (F : KeyedRomFamily) (C : RomChainedCarrier F) (Q : ℕ → ℕ)
    (A : Adversary (romChainedGame F C)) (hA : RomChainedEff F C Q A) :
    RomEff F.toRomFamily (fun l => Q l + (2 * C.len l + 2)) (chainedFinder F C A) := by
  obtain ⟨M, hMQ, hrun⟩ := hA
  refine ⟨fun l => OracleComp.bind (M l) (breakFinderComp C l), fun l => ?_, fun l H => ?_⟩
  · exact OracleComp.bind_queryBounded (hMQ l) (fun p => breakFinderComp_queryBounded C l p)
  · show (breakFinderComp C l (A.run l H)).eval H
      = (OracleComp.bind (M l) (breakFinderComp C l)).eval H
    rw [OracleComp.bind_eval, hrun l H]

/-! ## §4 — the binding, from the PROVED floor; and the counterexample dying at this layer. -/

/-- **⚑⚑ THE RE-GROUNDED CHAINED BINDING — from the KEYED, QUERY-COUNTED floor, WHICH IS PROVED.**

A chained-commitment forger in the query-bounded class has NEGLIGIBLE advantage: at a `λ`-bit
digest and a polynomial total budget `Q'` dominating the forger's queries PLUS the extractor's
re-walk, the chained commitment binds its whole payload — head and every block — except with
negligible probability. The floor is `keyedRom_hard` (the birthday bound, a theorem); efficiency is
discharged by `chainedFinder_in_romEff` (query accounting), not by pricing answer sizes. This is
what replaces `stateCommit_binds_from_polyTime`, whose `IsPolyTime` floor is FALSE at deployed
parameters (`Market.WideCommitBoundary.stateCommit_floor_polyTime_false_babyBear`). -/
theorem romChained_binds (F : KeyedRomFamily) (C : RomChainedCarrier F) (Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * C.len l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (A : Adversary (romChainedGame F C)) (hA : RomChainedEff F C Q A) :
    Negl (gameAdv (romChainedGame F C) A) := by
  have hfind : RomEff F.toRomFamily Q' (chainedFinder F C A) := by
    obtain ⟨M', hM'Q, hrun⟩ := chainedFinder_in_romEff F C Q A hA
    exact ⟨M', fun l => (hM'Q l).mono (hle l), hrun⟩
  exact negl_of_le (fun l => (gameAdv_mem_unit (romChainedGame F C) A l).1)
    (chained_adv_le F C A)
    (keyedRom_hard F Q' hQ' hw (chainedFinder F C A) hfind)

/-- **⚑ THE `Classical.choice` COLLISION-ANSWERER IS EXCLUDED AT THE CHAINED LAYER.** A chained
forger whose advantage is not negligible is NOT in the query-bounded class — were it inside,
`romChained_binds` would collapse its advantage. The strategy that refutes every `IsPolyTime`
floor (answer with a known collision of the fixed function) cannot produce a member of this class:
against the SAMPLED oracle it would have to know a collision it never queried, and
`RomOracle.OracleComp.eval_congr_of_agree_on_queried` forbids that. -/
theorem romChained_choiceForger_excluded (F : KeyedRomFamily) (C : RomChainedCarrier F)
    (Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + (2 * C.len l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (A : Adversary (romChainedGame F C))
    (hnn : ¬ Negl (gameAdv (romChainedGame F C) A)) :
    ¬ RomChainedEff F C Q A :=
  fun hA => hnn (romChained_binds F C Q Q' hle hQ' hw A hA)

/-! ## §5 — non-vacuity: the class is inhabited, the game is winnable, the admitted shape is
defanged. -/

/-- The fixed-answer chained forger — the `RomChainedEff` transplant of `fixedPairComp`: a 0-query
tree returning a fixed context and payload pair. -/
def fixedChainedComp (F : KeyedRomFamily) (C : RomChainedCarrier F)
    (c : ∀ l, C.Ctx l) (v v' : ∀ l, C.Val l) : RomChainedComp F C :=
  fun l => OracleComp.pure (c l, v l, v' l)

/-- **(TOOTH — the class is inhabited.)** The fixed-answer forger is a 0-query tree, hence in
`RomChainedEff` at every budget. The class the binding quantifies over is not `⊥`. -/
theorem fixedChainedForger_in_eff (F : KeyedRomFamily) (C : RomChainedCarrier F) (Q : ℕ → ℕ)
    (c : ∀ l, C.Ctx l) (v v' : ∀ l, C.Val l) :
    RomChainedEff F C Q (romChainedAdv F C (fixedChainedComp F C c v v')) :=
  ⟨fixedChainedComp F C c v v', fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩

/-- **(TOOTH — the admitted refuter-shape is DEFANGED, not excluded.)** The fixed-answer forger IS
in the class, and by the binding its advantage is negligible: the exact shape that wins with
probability `1` against a FIXED public hash wins only negligibly against the SAMPLED oracle.
Sampling after the adversary is fixed is what does the work — same verdict as
`KeyedRomFloor.fixedPairAdv_negl`, now at the chained binding layer. -/
theorem fixedChainedForger_negl (F : KeyedRomFamily) (C : RomChainedCarrier F) (Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * C.len l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (c : ∀ l, C.Ctx l) (v v' : ∀ l, C.Val l) :
    Negl (gameAdv (romChainedGame F C) (romChainedAdv F C (fixedChainedComp F C c v v'))) :=
  romChained_binds F C Q Q' hle hQ' hw _ (fixedChainedForger_in_eff F C Q c v v')

/-- **(TOOTH — the game is genuinely winnable.)** At the CONSTANT oracle every pair of distinct
payloads equivocates: the chain forgets its input the moment the digests agree, and at a constant
oracle they agree from the first query on. So the win event whose probability the binding bounds is
NOT empty — `Negl` is earned against a live event, not vacuously. -/
theorem romChainedGame_win_at_const (F : KeyedRomFamily) (C : RomChainedCarrier F) (l : ℕ)
    (c : C.Ctx l) (v v' : C.Val l) (hne : v ≠ v') (r₀ : F.toRomFamily.R l) :
    (romChainedGame F C).wins l (fun _ => r₀) (c, v, v') := by
  refine ⟨hne, ?_⟩
  show C.enc l (fun _ => r₀) c v = C.enc l (fun _ => r₀) c v'
  simp only [RomChainedCarrier.enc]
  rw [chainEval_const, chainEval_const]

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  OracleComp.bind_eval,
  OracleComp.bind_queryBounded,
  chainComp_eval,
  chainComp_queryBounded,
  chainEval_const,
  RomChainedCarrier.blocks_length,
  RomChainedCarrier.commitComp_eval,
  RomChainedCarrier.commitComp_queryBounded,
  romChainedGame_wins_iff,
  chainCollComp_queryBounded,
  chainCollComp_eval_collides,
  breakFinderComp_queryBounded,
  breakFinderComp_eval_collides,
  chained_wins_imp,
  chained_adv_le,
  chainedFinder_in_romEff,
  romChained_binds,
  romChained_choiceForger_excluded,
  fixedChainedForger_in_eff,
  fixedChainedForger_negl,
  romChainedGame_win_at_const
]

end Dregg2.Crypto.RomChainedReduction
