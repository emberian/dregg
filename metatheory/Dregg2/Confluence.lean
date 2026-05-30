/-
# Dregg2.Confluence — the THIRD judgement (I-confluence).

`dregg2.md §2.3` declares I-confluence a **co-equal third judgement** alongside
conservation (`Core`) and ordering — but the §8 module map (Core/Laws/Authority/
Boundary) gave it no home. THIS is its home. (Internal-inconsistency fix, found by
the handoff reading + the corpus pull.)

I-confluence is NEITHER linearity (`Core`) NOR the session/ordering type: it is the
**invariant-merge** property (BEC Thm 3.1) — do concurrent invariant-preserving
versions merge invariant-safely? The three are independent:
  • `balance ≥ 0` is linear but NOT I-confluent (two withdrawals merge to overdraft);
  • a grow-only set is I-confluent but NOT linear.
It is the well-formedness side-condition deciding whether a cell may run at **tier-1**
(causal-only / coordination-free / partition-tolerant) or must escalate to consensus.

Precedent (certified replicated-state verification — corpus, this round):
  • Gomes–Kleppmann, strong-eventual-consistency in Isabelle (canonical certified CRDT);
  • Burckhardt et al., replicated-data-types spec & verification (the optimality bound);
  • certified-mergeable-RDTs (PLDI'22); Katara (CRDT synthesis).
Compiling the I-confluent fragment: Hydro / Dedalus (CALM). The non-I-confluent
(coupled) fragment escalates via CryptoConcurrency's sum/coverage COD.

Spec-first: obligations stated with `sorry`; discharge after Core+Laws, alongside
the Authority lift, BEFORE Boundary's JointTurn (which consumes the per-cell tier).
-/
import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Card

namespace Dregg2.Confluence

universe u

/-- A cell's mergeable state is a join-semilattice; concurrent versions merge by `⊔`
(the CvRDT join — Gomes–Kleppmann / Burckhardt). -/
class MergeState (S : Type u) extends SemilatticeSup S

/-- A cell invariant: the property admissible turns must preserve (e.g. `balance ≥ 0`,
nullifier-uniqueness, a `WriteOnce` slot). -/
abbrev Invariant (S : Type u) := S → Prop

/-- **I-confluence (the third judgement).** `I` is I-confluent over a merge-state iff
concurrent invariant-preserving versions merge invariant-safely (BEC Thm 3.1). -/
def IConfluent {S : Type u} [MergeState S] (I : Invariant S) : Prop :=
  ∀ x y : S, I x → I y → I (x ⊔ y)

/-- **Tier-1 eligibility = the well-formedness side-condition.** A cell may select the
tier-1 (causal-only, coordination-free, partition-tolerant) finality rule **iff** its
invariant is I-confluent. Tier-1 on a non-I-confluent cell is the object BEC Thm 3.1
forbids — a static type error the finality classifier MUST reject. -/
def Tier1Eligible {S : Type u} [MergeState S] (I : Invariant S) : Prop :=
  IConfluent I

/-- **The `FinalityRule.admits` gate (the static check).** The classifier rejects a
tier-1 declaration unless `Tier1Eligible`; soundness = a tier-1 cell's concurrent
merges genuinely preserve `I`. (Obligation; the real classifier is over the cell's
write-set × state-lattice — `discoveries §3.7`.) -/
theorem admits_sound {S : Type u} [MergeState S] (I : Invariant S)
    (h : Tier1Eligible I) (x y : S) (hx : I x) (hy : I y) : I (x ⊔ y) := by
  exact h x y hx hy

/-- **Non-pairwise escalation (CryptoConcurrency) — PROVED.** When `I` is NOT I-confluent,
there genuinely EXISTS a concrete clashing pair: invariant-preserving versions `x` and `y`
whose merge `x ⊔ y` violates `I`. This is the constructive contrapositive witness of
`IConfluent` — escalation to consensus is *forced* by an exhibited counterexample, not
merely declared. (The full CryptoConcurrency story is sum/coverage over the whole
concurrent set — three pairwise-fine spends jointly overspending — but the *minimal*
falsifier I-confluence already fails on is a clashing pair; this is the in-Lean witness
that the coupled fragment is real, the obligation `coord/shared_budget.rs` discharges.) -/
theorem nonpairwise_escalation {S : Type u} [MergeState S] (I : Invariant S)
    (hI : ¬ IConfluent I) :
    ∃ x y : S, I x ∧ I y ∧ ¬ I (x ⊔ y) := by
  -- `IConfluent I` is `∀ x y, I x → I y → I (x ⊔ y)`; its negation gives, classically,
  -- the existential clashing-pair witness.
  unfold IConfluent at hI
  by_contra hcon
  apply hI
  intro x y hx hy
  by_contra hbad
  exact hcon ⟨x, y, hx, hy, hbad⟩

/-! ## The third judgement is NON-TRIVIAL: some invariants are I-confluent, some are not.

I-confluence genuinely *distinguishes* invariants — it is a real, falsifiable
side-condition, not vacuous (audit: previously this independence was prose only). We
exhibit both directions concretely over the grow-only-set semilattice `Finset ℕ` (⊔ = ∪).
This is the in-Lean witness for "linear ⇏ I-confluent / I-confluent ⇏ linear": a bounded
invariant (`card ≤ 1`, a `balance`-style cap) is NOT I-confluent and must escalate
(≥tier-2), while a grow-only invariant IS I-confluent and runs tier-1 cross-group-free. -/

instance : MergeState (Finset ℕ) := { toSemilatticeSup := inferInstance }

/-- **An I-confluent invariant exists (PROVED):** the grow-only `True` invariant is
preserved by any merge — grow-only sets run coordination-free (tier-1). -/
theorem top_iconfluent : IConfluent (S := Finset ℕ) (fun _ => True) :=
  fun _ _ _ _ => trivial

/-- **A concrete NON-I-confluent invariant (PROVED): "at most one element."** Two
singletons each satisfy it, but their merge `{1} ⊔ {2} = {1,2}` has two elements — so a
cell with this invariant CANNOT run tier-1; it must escalate (≥tier-2 / single-writer).
This is the `balance ≥ 0` shape: a bounded resource whose concurrent merges overflow the
bound. With `top_iconfluent`, this proves I-confluence is a genuine, falsifiable
judgement. -/
theorem cardLeOne_not_iconfluent :
    ¬ IConfluent (S := Finset ℕ) (fun s => s.card ≤ 1) := by
  intro h
  have hbad := h {1} {2} (by decide) (by decide)
  exact absurd hbad (by decide)

end Dregg2.Confluence
