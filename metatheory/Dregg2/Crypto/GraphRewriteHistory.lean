/-
# Dregg2.Crypto.GraphRewriteHistory — root-linked receipts for semantic rewrite histories.

`Crypto.GraphRewrite` proves the semantic step relation: a licensed rule genuinely matches a host
graph, deletes its instantiated left-hand side, preserves a context, and glues its instantiated
right-hand side.  `Crypto.Chain` proves that a locally checkable `Cert R` chain is equivalent to the
reflexive-transitive closure of any relation `R`.

This file supplies the protocol bridge between those two facts and a public receipt stream.  A
`CertifiedStep` has a public statement `(session, rulesRoot, index, oldRoot, newRoot)` plus hidden
semantic openings `(oldGraph, newGraph)` and a sound `RewriteStep`.  Consecutive receipts must keep
the same session/rules root, increment the index exactly once, and connect `newRoot` to `oldRoot`.

The commitment boundary is deliberately not faked.  Equal graph roots imply equal semantic graphs
only under a supplied binding carrier (`Function.Injective commit` here, the idealized theorem shape
which a deployed hash instantiates computationally).  Without it, a root-linked semantic splice
extracts an explicit collision: two different graphs with the same commitment
(`hidden_splice_extracts_collision` — the extraction tooth, which NAMES the pair).  Under binding,
`linked_reduces` and `linked_has_cert` turn any nonempty receipt history into a genuine
`ReflTransGen (RewriteStep rules)` / `Hypergraph.Cert` from its first graph to its last.

## ⚑ The history soundness is now SPLIT: a pure core + a keyed-ROM reduction (07-24)

The former exports `linked_reduces_or_collision` / `linked_has_cert_or_collision` concluded
`… ∨ CommitCollision commit` with `CommitCollision = ∃ g h, g ≠ h ∧ commit g = commit h` — at any
deployed compressing root that existential is TRUE by pigeonhole, so both disjunctions held
through the collides branch with the semantic conclusion never forced.  A statement about
SOLUTIONS, where hardness quantifies over EFFICIENT ADVERSARIES.  DELETED (with the
`CommitCollision` shape itself), replaced by the honest split:

  * **the PURE core** — `reduces_of_adjacent_agree` / `has_cert_of_adjacent_agree`: a receipt
    history whose adjacent hidden endpoint graphs AGREE composes to a genuine reduction, with no
    hash anywhere; `adjacent_agree_of_linked_of_injective` recovers the agreement from root links
    under the idealized carrier (so `linked_reduces` is the composition of the two, unchanged);
  * **the PRICED escape** — §RomSuccessor: the ONLY way a linked history can fail the agreement is
    a SPLICE, and at the sampled keyed oracle the splice forger is a first-class `RomForgery`
    whose extractor is a pure post-map (`mapOut`, budget preserved) into the commitment carrier;
    `historySplice_binds_rom` closes it from the PROVED birthday floor (`keyedRom_hard` via
    `romCarrier_binds`).  ⚑ The modelling step is labelled (`RomCarrierSites` header): the sampled
    `H : Unit × Val → Fin (2 ^ l)` idealises the deployed graph root over a BOUNDED graph payload
    at asymptotic width; nothing is claimed about the fixed public hash.

This is independent of any particular AIR.  A bounded private graph-rewrite descriptor discharges
each receipt's `sound` field; the existing IVC segment chain carries the public roots.  The theorem
then supplies the semantic meaning of the folded history.
-/
import Dregg2.Crypto.GraphRewrite
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Tactics

namespace Dregg2.Crypto.GraphRewriteHistory

open Dregg2.Crypto.Hypergraph
open Dregg2.Crypto.GraphRewrite

/-- The public statement of one certified rewrite step.  `GraphRoot` is intended to be a faithful
eight-limb graph commitment and `RulesRoot` a faithful ruleset commitment; the theorem is agnostic
to their concrete encoding. -/
structure Statement (Session RulesRoot GraphRoot : Type) where
  session : Session
  rulesRoot : RulesRoot
  index : Nat
  oldRoot : GraphRoot
  newRoot : GraphRoot

/-- A public rewrite statement together with the hidden semantic openings and the proof meaning of
one accepted private leaf.  The graph values are witness-side data; only `stmt` is the receipt ABI. -/
structure CertifiedStep (Session RulesRoot : Type) {V L GraphRoot : Type}
    (Step : Hypergraph L V → Hypergraph L V → Prop)
    (commit : Hypergraph L V → GraphRoot) where
  stmt : Statement Session RulesRoot GraphRoot
  oldGraph : Hypergraph L V
  newGraph : Hypergraph L V
  oldRoot_binds : stmt.oldRoot = commit oldGraph
  newRoot_binds : stmt.newRoot = commit newGraph
  sound : Step oldGraph newGraph

namespace CertifiedStep

variable {V L Session RulesRoot GraphRoot : Type}
variable {Step : Hypergraph L V → Hypergraph L V → Prop}
variable {commit : Hypergraph L V → GraphRoot}

/-- The public view of a certified step; witness graphs and the semantic proof do not cross the
receipt boundary. -/
def publicStatement (s : CertifiedStep Session RulesRoot Step commit) :
    Statement Session RulesRoot GraphRoot :=
  s.stmt

end CertifiedStep

/-- Two consecutive receipts form one protocol link exactly when they stay in one session and one
ruleset, advance by one index, and identify the preceding output root with the next input root. -/
structure Link {V L Session RulesRoot GraphRoot : Type}
    {Step : Hypergraph L V → Hypergraph L V → Prop}
    {commit : Hypergraph L V → GraphRoot}
    (a b : CertifiedStep Session RulesRoot Step commit) : Prop where
  sameSession : b.stmt.session = a.stmt.session
  sameRules : b.stmt.rulesRoot = a.stmt.rulesRoot
  nextIndex : b.stmt.index = a.stmt.index + 1
  roots : a.stmt.newRoot = b.stmt.oldRoot

/-- Consecutive-link validity for a receipt list.  This intentionally mirrors
`Hypergraph.chain`; the latter is recovered semantically by `linked_has_cert`. -/
def Linked {V L Session RulesRoot GraphRoot : Type}
    {Step : Hypergraph L V → Hypergraph L V → Prop}
    {commit : Hypergraph L V → GraphRoot} :
    List (CertifiedStep Session RulesRoot Step commit) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Link a b ∧ Linked (b :: rest)

/-- The semantic end graph of a nonempty history represented as its first step and remaining
steps. -/
def endGraph {V L Session RulesRoot GraphRoot : Type}
    {Step : Hypergraph L V → Hypergraph L V → Prop}
    {commit : Hypergraph L V → GraphRoot}
    (head : CertifiedStep Session RulesRoot Step commit) :
    List (CertifiedStep Session RulesRoot Step commit) → Hypergraph L V
  | [] => head.newGraph
  | next :: rest => endGraph next rest

section Refusals

variable {V L Session RulesRoot GraphRoot : Type}
variable {Step : Hypergraph L V → Hypergraph L V → Prop}
variable {commit : Hypergraph L V → GraphRoot}
variable {a b : CertifiedStep Session RulesRoot Step commit}

/-- A ruleset substitution cannot be a valid link. -/
theorem wrong_rules_refused (h : b.stmt.rulesRoot ≠ a.stmt.rulesRoot) : ¬ Link a b :=
  fun hlink => h hlink.sameRules

/-- A cross-session splice cannot be a valid link. -/
theorem wrong_session_refused (h : b.stmt.session ≠ a.stmt.session) : ¬ Link a b :=
  fun hlink => h hlink.sameSession

/-- Reordering, replaying, or skipping a receipt cannot be a valid link: the next index is exact. -/
theorem wrong_index_refused (h : b.stmt.index ≠ a.stmt.index + 1) : ¬ Link a b :=
  fun hlink => h hlink.nextIndex

/-- A public endpoint splice with unequal roots cannot be a valid link. -/
theorem wrong_root_refused (h : a.stmt.newRoot ≠ b.stmt.oldRoot) : ¬ Link a b :=
  fun hlink => h hlink.roots

/-- **The honest hash boundary.**  If roots link but the hidden semantic endpoint graphs differ,
the two openings are an explicit collision in `commit`. -/
theorem hidden_splice_extracts_collision (hlink : Link a b)
    (hne : a.newGraph ≠ b.oldGraph) :
    a.newGraph ≠ b.oldGraph ∧ commit a.newGraph = commit b.oldGraph := by
  refine ⟨hne, ?_⟩
  calc
    commit a.newGraph = a.stmt.newRoot := a.newRoot_binds.symm
    _ = b.stmt.oldRoot := hlink.roots
    _ = commit b.oldGraph := b.oldRoot_binds

/-- Under the idealized binding carrier, a public root link identifies the two semantic endpoint
graphs.  A deployed sponge uses this lemma through its collision-resistance/extractability theorem,
not by claiming mathematical injectivity of a finite hash. -/
theorem linked_graph_eq (hcommit : Function.Injective commit) (hlink : Link a b) :
    a.newGraph = b.oldGraph := by
  apply hcommit
  calc
    commit a.newGraph = a.stmt.newRoot := a.newRoot_binds.symm
    _ = b.stmt.oldRoot := hlink.roots
    _ = commit b.oldGraph := b.oldRoot_binds

end Refusals

section HistorySoundness

variable {V L Session RulesRoot GraphRoot : Type}
variable {Step : Hypergraph L V → Hypergraph L V → Prop}
variable {commit : Hypergraph L V → GraphRoot}

/-- **Adjacent hidden agreement** — every consecutive pair of receipts agrees on its hidden
endpoint graphs.  The SEMANTIC half of the deleted disjunction's binding branch, isolated: it
mentions no hash, no root, no crypto. -/
def AdjacentAgree :
    List (CertifiedStep Session RulesRoot Step commit) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a.newGraph = b.oldGraph ∧ AdjacentAgree (b :: rest)

/-- **THE PURE CORE — an adjacent-agreeing history composes.**  Each receipt contributes one real
`RewriteStep`; agreement identifies the endpoints; `ReflTransGen.head` composes.  No commitment
appears: this is the deterministic content the deleted `linked_reduces_or_collision` mixed with
its pigeonhole escape branch. -/
theorem reduces_of_adjacent_agree :
    ∀ (head : CertifiedStep Session RulesRoot Step commit)
      (rest : List (CertifiedStep Session RulesRoot Step commit)),
      AdjacentAgree (head :: rest) →
      Relation.ReflTransGen Step head.oldGraph (endGraph head rest) := by
  intro head rest
  induction rest generalizing head with
  | nil =>
      intro _
      exact Relation.ReflTransGen.head head.sound Relation.ReflTransGen.refl
  | cons next rest ih =>
      intro hagree
      have hEq : head.newGraph = next.oldGraph := hagree.1
      have hrest := ih next hagree.2
      have hsound := head.sound
      rw [hEq] at hsound
      exact Relation.ReflTransGen.head hsound hrest

/-- The pure core, in the repository's common certificate form. -/
theorem has_cert_of_adjacent_agree
    (head : CertifiedStep Session RulesRoot Step commit)
    (rest : List (CertifiedStep Session RulesRoot Step commit))
    (hagree : AdjacentAgree (head :: rest)) :
    ∃ c, Cert Step head.oldGraph (endGraph head rest) c :=
  (bridge Step head.oldGraph (endGraph head rest)).mpr
    (reduces_of_adjacent_agree head rest hagree)

/-- **Root links force adjacent agreement under the idealized carrier** — the strength bridge from
the public receipt discipline to the pure core.  A deployed root instantiates this through the
§RomSuccessor reduction (negligibly-failing agreement), never through injectivity of a finite
hash. -/
theorem adjacent_agree_of_linked_of_injective (hcommit : Function.Injective commit) :
    ∀ (hist : List (CertifiedStep Session RulesRoot Step commit)),
      Linked hist → AdjacentAgree hist
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: b :: rest, hlinked =>
      ⟨linked_graph_eq hcommit hlinked.1,
        adjacent_agree_of_linked_of_injective hcommit (b :: rest) hlinked.2⟩

/-- **A root-linked certified history is a genuine semantic graph-rewrite reduction**, under the
explicit commitment-binding carrier: the composition of the strength bridge and the pure core. -/
theorem linked_reduces (hcommit : Function.Injective commit)
    (head : CertifiedStep Session RulesRoot Step commit)
    (rest : List (CertifiedStep Session RulesRoot Step commit))
    (hlinked : Linked (head :: rest)) :
    Relation.ReflTransGen Step head.oldGraph (endGraph head rest) :=
  reduces_of_adjacent_agree head rest
    (adjacent_agree_of_linked_of_injective hcommit (head :: rest) hlinked)

/-- The same result in the repository's common certificate form: every valid root-linked receipt
history has a locally checkable `Hypergraph.Cert` chain for the semantic rewrite relation. -/
theorem linked_has_cert (hcommit : Function.Injective commit)
    (head : CertifiedStep Session RulesRoot Step commit)
    (rest : List (CertifiedStep Session RulesRoot Step commit))
    (hlinked : Linked (head :: rest)) :
    ∃ c, Cert Step head.oldGraph (endGraph head rest) c :=
  (bridge Step head.oldGraph (endGraph head rest)).mpr
    (linked_reduces hcommit head rest hlinked)

end HistorySoundness

/-! ## ⚑ §RomSuccessor — the SPLICE, PRICED on the PROVED keyed-ROM floor.

The pure core needs `AdjacentAgree`; the receipt discipline supplies root LINKS.  The only gap is
a SPLICE: a linked history in which some adjacent pair hides two DIFFERENT graphs behind one
root.  The deleted disjunctions let that gap escape through `∃ collision` (unconditionally true
at a compressing root).  Here the splice is a first-class forgery at the SAMPLED oracle: the
forger outputs a whole receipt history, the win relation checks the links, the bindings against
the sampled oracle, and the presence of a splice — and the extractor hands the spliced pair to
the commitment carrier as a pure post-map.  `keyedRom_hard` (the birthday bound) kills it. -/

section RomSuccessor

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomCarrierSites

variable (Val : Type) [Fintype Val] [DecidableEq Val] [Nonempty Val]
variable (Session RulesRoot : Type) [DecidableEq Session] [DecidableEq RulesRoot]

/-- **THE HISTORY KEYED ROM FAMILY** — the graph commitment as a sampled oracle over a BOUNDED
graph payload `Val` (⚑ the labelled modelling step: the deployed root hash idealised at
asymptotic width over the bounded graph code the receipts actually commit). -/
def historyRomFamily : KeyedRomFamily :=
  flatFamily Unit inferInstance inferInstance ⟨()⟩ (fun _ => Val)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)

/-- The family's width obligation, closed by construction. -/
theorem historyRomFamily_card_R (l : ℕ) :
    letI := (historyRomFamily Val).rFin l
    Fintype.card ((historyRomFamily Val).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- One receipt at the sampled oracle: the public statement (roots now live in the ideal digest
space) plus the two hidden graph payloads.  The ROM face of `CertifiedStep`, minus the semantic
`sound` field — the splice game is about the COMMITMENT layer only (the semantics stay in the
pure core). -/
structure RomStep (l : ℕ) where
  session : Session
  rulesRoot : RulesRoot
  index : ℕ
  oldRoot : Fin (2 ^ l)
  newRoot : Fin (2 ^ l)
  oldGraph : Val
  newGraph : Val
  deriving DecidableEq

/-- One protocol link between consecutive ROM receipts — `Link`, decided. -/
def romLinkB {l : ℕ} (a b : RomStep Val Session RulesRoot l) : Bool :=
  decide (b.session = a.session) && decide (b.rulesRoot = a.rulesRoot)
    && decide (b.index = a.index + 1) && decide (a.newRoot = b.oldRoot)

/-- Consecutive-link validity for a ROM receipt list — `Linked`, decided. -/
def romLinkedB {l : ℕ} : List (RomStep Val Session RulesRoot l) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => romLinkB Val Session RulesRoot a b && romLinkedB (b :: rest)

/-- Every receipt's roots genuinely bind its hidden graphs AT THE SAMPLED ORACLE.  This is where
the oracle enters the win relation — the composed check no single carrier could state. -/
def romBindsB {l : ℕ} (H : Unit × Val → Fin (2 ^ l)) :
    List (RomStep Val Session RulesRoot l) → Bool
  | [] => true
  | s :: rest =>
      decide (H ((), s.oldGraph) = s.oldRoot) && decide (H ((), s.newGraph) = s.newRoot)
        && romBindsB H rest

/-- **THE SPLICE FINDER** — the first adjacent pair hiding two DIFFERENT graphs.  TOTAL and pure:
the pair sits inside the forger's own answer. -/
def spliceFind {l : ℕ} : List (RomStep Val Session RulesRoot l) → Option (Val × Val)
  | a :: b :: rest =>
      if a.newGraph = b.oldGraph then spliceFind (b :: rest)
      else some (a.newGraph, b.oldGraph)
  | _ => none

omit [Fintype Val] [Nonempty Val] in
/-- **THE SPLICED PAIR IS A COLLISION AT THE SAMPLED ORACLE** — the win-preservation core: in a
linked, oracle-bound history, whatever pair `spliceFind` returns consists of two DISTINCT
payloads with ONE digest (the shared root between the two receipts). -/
theorem spliceFind_collides {l : ℕ} (H : Unit × Val → Fin (2 ^ l)) :
    ∀ (hist : List (RomStep Val Session RulesRoot l)),
      romLinkedB Val Session RulesRoot hist = true →
      romBindsB Val Session RulesRoot H hist = true →
      ∀ g h : Val, spliceFind Val Session RulesRoot hist = some (g, h) →
        g ≠ h ∧ H ((), g) = H ((), h) := by
  intro hist
  induction hist with
  | nil =>
      intro _ _ g h hfind
      simp [spliceFind] at hfind
  | cons a rest ih =>
      cases rest with
      | nil =>
          intro _ _ g h hfind
          simp [spliceFind] at hfind
      | cons b rest' =>
          intro hlinked hbinds g h hfind
          rw [show romLinkedB Val Session RulesRoot (a :: b :: rest')
                = (romLinkB Val Session RulesRoot a b
                    && romLinkedB Val Session RulesRoot (b :: rest')) from rfl,
            Bool.and_eq_true] at hlinked
          rw [show romBindsB Val Session RulesRoot H (a :: b :: rest')
                = (decide (H ((), a.oldGraph) = a.oldRoot)
                    && decide (H ((), a.newGraph) = a.newRoot)
                    && romBindsB Val Session RulesRoot H (b :: rest')) from rfl,
            Bool.and_eq_true, Bool.and_eq_true] at hbinds
          by_cases hEq : a.newGraph = b.oldGraph
          · rw [show spliceFind Val Session RulesRoot (a :: b :: rest')
                  = (if a.newGraph = b.oldGraph
                     then spliceFind Val Session RulesRoot (b :: rest')
                     else some (a.newGraph, b.oldGraph)) from rfl,
              if_pos hEq] at hfind
            exact ih hlinked.2 hbinds.2 g h hfind
          · rw [show spliceFind Val Session RulesRoot (a :: b :: rest')
                  = (if a.newGraph = b.oldGraph
                     then spliceFind Val Session RulesRoot (b :: rest')
                     else some (a.newGraph, b.oldGraph)) from rfl,
              if_neg hEq] at hfind
            have hpair := Option.some.inj hfind
            have hg : a.newGraph = g := congrArg Prod.fst hpair
            have hh : b.oldGraph = h := congrArg Prod.snd hpair
            subst hg; subst hh
            refine ⟨hEq, ?_⟩
            have hlink := hlinked.1
            simp only [romLinkB, Bool.and_eq_true, decide_eq_true_eq] at hlink
            have hbindsTail := hbinds.2
            rw [show romBindsB Val Session RulesRoot H (b :: rest')
                  = (decide (H ((), b.oldGraph) = b.oldRoot)
                      && decide (H ((), b.newGraph) = b.newRoot)
                      && romBindsB Val Session RulesRoot H rest') from rfl,
              Bool.and_eq_true, Bool.and_eq_true] at hbindsTail
            have h1 : H ((), a.newGraph) = a.newRoot := of_decide_eq_true hbinds.1.2
            have h2 : H ((), b.oldGraph) = b.oldRoot := of_decide_eq_true hbindsTail.1.1
            rw [h1, h2]
            exact hlink.2

/-- **THE SPLICE FORGERY** — the forger outputs a WHOLE receipt history; it WINS iff the history
is linked, every root binds its hidden graph at the sampled oracle, and some adjacent pair is
spliced.  The deployed break — passing off a discontinuous history as a valid receipt stream —
IS the win relation. -/
def historySpliceForgery : RomForgery (historyRomFamily Val) where
  Ans := fun l => List (RomStep Val Session RulesRoot l)
  wins := fun _ H hist =>
    romLinkedB Val Session RulesRoot hist = true
      ∧ romBindsB Val Session RulesRoot H hist = true
      ∧ (spliceFind Val Session RulesRoot hist).isSome = true
  winsDec := fun _ _ _ => by infer_instance

/-- The splice break game. -/
abbrev historySpliceGame : Game := (historySpliceForgery Val Session RulesRoot).game

/-- **THE EXTRACTOR** — read the spliced pair off the forger's answer (identity-carrier triple);
a pure output reshaping, so the query budget is PRESERVED (`mapOut`). -/
noncomputable def spliceExtract (l : ℕ) (hist : List (RomStep Val Session RulesRoot l)) :
    (idRomCarrier (historyRomFamily Val)).Ctx l
      × (idRomCarrier (historyRomFamily Val)).Val l
      × (idRomCarrier (historyRomFamily Val)).Val l :=
  match spliceFind Val Session RulesRoot hist with
  | some (g, h) => ((), ((), g), ((), h))
  | none => ((), ((), Classical.arbitrary Val), ((), Classical.arbitrary Val))

/-- **⚑⚑ THE SPLICE BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the deleted
`linked_reduces_or_collision` / `linked_has_cert_or_collision`: every query-bounded forger that
produces a LINKED, oracle-BOUND, SPLICED receipt history has NEGLIGIBLE advantage.  Combined with
the pure core: except with negligible probability, a linked history that binds its roots at the
sampled oracle has NO splice, hence `AdjacentAgree`, hence (`reduces_of_adjacent_agree`) a
genuine semantic reduction.  NO floor hypothesis, NO escape branch. -/
theorem historySplice_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (historySpliceGame Val Session RulesRoot))
    (hA : RomForgeryEff (historyRomFamily Val) (historySpliceForgery Val Session RulesRoot) Q A) :
    Negl (gameAdv (historySpliceGame Val Session RulesRoot) A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine negl_of_le
    (fun l => (gameAdv_mem_unit (historySpliceGame Val Session RulesRoot) A l).1)
    (fun l => ?_)
    (romCarrier_binds (historyRomFamily Val) (idRomCarrier _) Q hQ
      (historyRomFamily_card_R Val)
      (romCarrierAdv _ _
        (fun l => OracleComp.mapOut (spliceExtract Val Session RulesRoot l) (M l)))
      ⟨fun l => OracleComp.mapOut (spliceExtract Val Session RulesRoot l) (M l),
        fun l => OracleComp.mapOut_queryBounded _ (hM l), fun _ _ => rfl⟩)
  refine @winProb_le_of_imp _ ((historySpliceGame Val Session RulesRoot).instFin l) _ _
    (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hlinked, hbinds, hsplice⟩ := hH
  have hBrun : (romCarrierAdv _ _
      (fun l => OracleComp.mapOut (spliceExtract Val Session RulesRoot l) (M l))).run l H
      = spliceExtract Val Session RulesRoot l (A.run l H) := by
    show (OracleComp.mapOut (spliceExtract Val Session RulesRoot l) (M l)).eval H = _
    erw [OracleComp.mapOut_eval, hrun l H]
    rfl
  rw [hBrun]
  obtain ⟨⟨g, h⟩, hfind⟩ := Option.isSome_iff_exists.mp hsplice
  obtain ⟨hne, hcoll⟩ :=
    spliceFind_collides Val Session RulesRoot H (A.run l H) hlinked hbinds g h hfind
  unfold spliceExtract
  rw [hfind]
  exact ⟨fun hc => hne (congrArg Prod.snd hc), hcoll⟩

/-- The two-receipt SPLICED demonstration history: both receipts carry one root value, the first
hides `v` as its output graph, the second hides `w ≠ v` as its input graph. -/
def constSpliceHist (s : Session) (rr : RulesRoot) (v w : Val) (l : ℕ) :
    List (RomStep Val Session RulesRoot l) :=
  [⟨s, rr, 0, ⟨0, by positivity⟩, ⟨0, by positivity⟩, v, v⟩,
   ⟨s, rr, 1, ⟨0, by positivity⟩, ⟨0, by positivity⟩, w, w⟩]

/-- **(TOOTH — the game is WINNABLE and the admitted refuter-shape is DEFANGED.)** With two
distinct payloads, the `0`-query constant answerer emitting the two-receipt SPLICED history is IN
the class, WINS at the constant oracle (every digest is the shared root), and is NEGLIGIBLE by
the bound — the strategy that made the deleted `∃ collision` branch a free pass dies at the
sampled oracle. -/
theorem historySplice_constAnswer_defanged (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (s : Session) (rr : RulesRoot) (v w : Val) (hvw : v ≠ w) :
    (RomForgeryEff (historyRomFamily Val) (historySpliceForgery Val Session RulesRoot) Q
        ⟨fun l _ => constSpliceHist Val Session RulesRoot s rr v w l⟩)
      ∧ (∀ l, 0 < gameAdv (historySpliceGame Val Session RulesRoot)
          ⟨fun l _ => constSpliceHist Val Session RulesRoot s rr v w l⟩ l)
      ∧ Negl (gameAdv (historySpliceGame Val Session RulesRoot)
          ⟨fun l _ => constSpliceHist Val Session RulesRoot s rr v w l⟩) := by
  have hmem : RomForgeryEff (historyRomFamily Val)
      (historySpliceForgery Val Session RulesRoot) Q
      ⟨fun l _ => constSpliceHist Val Session RulesRoot s rr v w l⟩ :=
    ⟨fun l => OracleComp.pure (constSpliceHist Val Session RulesRoot s rr v w l),
      fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩
  refine ⟨hmem, fun l => ?_, historySplice_binds_rom Val Session RulesRoot Q hQ _ hmem⟩
  refine @winProb_pos_of_witness _ ((historySpliceGame Val Session RulesRoot).instFin l) _
    (fun _ => ⟨0, by positivity⟩) ?_
  refine (Adversary.hit_eq_true _ l _).mpr ⟨?_, ?_, ?_⟩
  · simp [constSpliceHist, romLinkedB, romLinkB]
  · simp [constSpliceHist, romBindsB]
  · simp [constSpliceHist, spliceFind, hvw]

/-- **(TOOTH — a non-negligible splice forger is OUTSIDE the class.)** -/
theorem historySplice_nonNegl_forger_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (historySpliceGame Val Session RulesRoot))
    (hnn : ¬ Negl (gameAdv (historySpliceGame Val Session RulesRoot) A)) :
    ¬ RomForgeryEff (historyRomFamily Val) (historySpliceForgery Val Session RulesRoot) Q A :=
  fun hA => hnn (historySplice_binds_rom Val Session RulesRoot Q hQ A hA)

end RomSuccessor

/-! ## Non-vacuity — the byte-graph rewrite from `GraphRewrite.Reference` as a receipt history. -/

namespace Reference

open Dregg2.Crypto.GraphRewrite.Reference

/-- For the non-vacuity witness only, commit a graph to its complete edge list.  This is genuinely
injective and keeps the example free of a cryptographic assumption; deployed histories use a
faithful root plus the collision theorem above. -/
def edgeCommit (g : Hypergraph UInt8 UInt8) : List (Hyperedge UInt8 UInt8) := g.edges

theorem edgeCommit_injective : Function.Injective edgeCommit := by
  intro a b h
  cases a with
  | mk ae =>
      cases b with
      | mk be =>
          simp only [edgeCommit] at h
          subst h
          rfl

def refStmt : Statement Unit Nat (List (Hyperedge UInt8 UInt8)) where
  session := ()
  rulesRoot := 7
  index := 0
  oldRoot := edgeCommit g0
  newRoot := edgeCommit g1

def refStep : CertifiedStep Unit Nat (RewriteStep [splitRule]) edgeCommit where
  stmt := refStmt
  oldGraph := g0
  newGraph := g1
  oldRoot_binds := rfl
  newRoot_binds := rfl
  sound := g0_rewrites_g1

theorem reference_history_reduces :
    Relation.ReflTransGen (RewriteStep [splitRule]) g0 g1 := by
  simpa [refStep, endGraph] using
    linked_reduces edgeCommit_injective refStep [] (by trivial)

theorem reference_history_has_cert :
    ∃ c, Cert (RewriteStep [splitRule]) g0 g1 c := by
  simpa [refStep, endGraph] using
    linked_has_cert edgeCommit_injective refStep [] (by trivial)

end Reference

#assert_all_clean [
  wrong_rules_refused,
  wrong_session_refused,
  wrong_index_refused,
  wrong_root_refused,
  hidden_splice_extracts_collision,
  linked_graph_eq,
  reduces_of_adjacent_agree,
  has_cert_of_adjacent_agree,
  adjacent_agree_of_linked_of_injective,
  linked_reduces,
  linked_has_cert,
  historyRomFamily_card_R,
  spliceFind_collides,
  historySplice_binds_rom,
  historySplice_constAnswer_defanged,
  historySplice_nonNegl_forger_excluded,
  Reference.edgeCommit_injective,
  Reference.reference_history_reduces,
  Reference.reference_history_has_cert
]

end Dregg2.Crypto.GraphRewriteHistory
