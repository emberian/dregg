/-
# VeilBridge.Ring: Veil's ring leader-election model under breadstuffs' CTL

Veil's tutorial protocol (`Examples/Tutorial/Ring.lean`, leader election on a unidirectional ring),
read through `VeilBridge.toSystem`. Its safety property `single_leader` ("at most one leader"), the
very predicate Veil's `#check_invariants` discharges, is stated here as breadstuffs' branching-time
`AG` at every initial state, and `invariant_iff_AG` makes it the same proposition as Veil's
invariant. Nothing new is proved about the protocol: this file shows the two worlds typecheck one
statement over one definition.
-/
import VeilBridge.CTL
import Examples.Tutorial.Ring

namespace VeilBridge.RingCTL

-- Veil registers the abstract-state field representations as module-local instances; the
-- predicates below are stated over the same abstract state, so bring them into scope here.
attribute [local instance] Ring.instAbstractFieldRepresentation Ring.instLawfulAbstractFieldRepresentation

variable (node : Type) [DecidableEq node] [Inhabited node] [TotalOrder node] [Between node]

/-- Veil's generated relational transition system for the ring protocol. -/
noncomputable abbrev ringSys := Ring.relationalTransitionSystem node

/-- Veil's `single_leader` safety predicate, as a set of ring states at background theory `th`. -/
def SingleLeader (th : Ring.Theory node) : Set (Ring.State (Ring.FieldAbstractType node)) :=
  { s | Ring.single_leader (ρ := Ring.Theory node) (σ := Ring.State (Ring.FieldAbstractType node))
          th s }

/-- Veil's ring safety invariant is breadstuffs' `AG single_leader` at every initial state. -/
theorem single_leader_invariant_iff_AG (th : Ring.Theory node) :
    (∀ s, (ringSys node).reachable th s → s ∈ SingleLeader node th) ↔
      (∀ s₀, (ringSys node).assumptions th → (ringSys node).init th s₀ →
        s₀ ∈ Dregg2.Proof.CTL.AG (toSystem (ringSys node) th) (SingleLeader node th)) :=
  invariant_iff_AG (ringSys node) th (SingleLeader node th)

#assert_all_clean [single_leader_invariant_iff_AG]

end VeilBridge.RingCTL
