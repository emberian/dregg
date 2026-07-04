/-
LbCorrect — load-balancer selection CORRECTNESS.

`Rendezvous` and `Wrr` already carry SAFETY-shaped theorems (totality,
membership, minimal disruption, window fairness). This module lifts the claim
to CORRECTNESS: the backend the implementation selects is *exactly* the one an
INDEPENDENT specification of the selection rule dictates — a refinement
`impl = spec`, not a test and not a well-formedness bound.

Two policies are covered.

  * Rendezvous / highest-random-weight (HRW), after Thaler & Ravishankar
    ("Using name-based mappings to increase hit rates", IEEE/ACM ToN 6(1),
    1998): the selected backend is the ARGMAX of the per-candidate score
    `hash key b.id` over the eligible set. `specRendezvous` is that argmax,
    written as a running-maximum scan with NO reference to `rendezvous` or to
    its `beats` comparator; `rendezvous_refines_spec` proves the two agree.

  * Weighted round-robin: residue `r = round mod totalWeight` selects the
    backend whose cumulative-weight INTERVAL `[prefix, prefix + weight)`
    contains `r`. `specWrr` decides interval membership from absolute prefix
    offsets; `wrr_refines_spec` proves it equals the implementation's
    subtractive walk `pickByResidue`.

Each refinement is NON-VACUOUS: a "return the first candidate" or a "return the
hash-minimum" selector fails it (witnessed by the concrete `example`s at the
end), and neither spec is the implementation renamed — the HRW spec ranks by a
scalar key with a left-to-right running maximum, the WRR spec tests absolute
prefix intervals, while the implementations recurse structurally through
`beats` and through relative subtraction respectively.
-/

import Proxy.Rendezvous
import Proxy.Wrr

namespace Proxy

/-! ## Rendezvous / HRW: refinement against an argmax specification -/

/-- The scalar key HRW ranks a candidate by: its hash score `hash key b.id`,
paired with the stable id as the deterministic tie-breaker (HRW resolves the
measure-zero score ties by a fixed rule; the larger id is one such rule). This
pair is the quantity the policy MAXIMIZES. -/
def hrwKey (hash : Nat → Nat → Nat) (key : Nat) (b : Backend) : Nat × Nat :=
  (hash key b.id, b.id)

/-- Non-strict lexicographic `≥` on `(score, id)` keys. -/
def keyGe (p q : Nat × Nat) : Bool :=
  decide (q.1 < p.1) || (decide (p.1 = q.1) && decide (q.2 ≤ p.2))

theorem keyGe_refl (p : Nat × Nat) : keyGe p p = true := by
  simp [keyGe]

theorem keyGe_trans {p q r : Nat × Nat}
    (h1 : keyGe p q = true) (h2 : keyGe q r = true) : keyGe p r = true := by
  simp only [keyGe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem keyGe_total (p q : Nat × Nat) (h : keyGe p q = false) :
    keyGe q p = true := by
  simp only [keyGe, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at h
  simp only [keyGe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- One running-maximum step: keep the incumbent unless the new candidate's key
is `≥` it (ties go to the later candidate — a stable last-writer rule). -/
def argmaxStep (hash : Nat → Nat → Nat) (key : Nat)
    (best : Option Backend) (b : Backend) : Option Backend :=
  match best with
  | none => some b
  | some a => if keyGe (hrwKey hash key b) (hrwKey hash key a) then some b else some a

/-- **Independent HRW specification.** The selected backend is the ARGMAX of the
hash score over the candidate list: scan left to right keeping the candidate
whose `(score, id)` key is maximal. Defined WITHOUT `rendezvous` or `beats`. -/
def specRendezvous (hash : Nat → Nat → Nat) (key : Nat)
    (bs : List Backend) : Option Backend :=
  bs.foldl (argmaxStep hash key) none

/-- A `some`-seeded step always yields `some (…)`. -/
theorem argmaxStep_some (hash : Nat → Nat → Nat) (key : Nat) (a x : Backend) :
    argmaxStep hash key (some a) x
      = some (if keyGe (hrwKey hash key x) (hrwKey hash key a) then x else a) := by
  simp only [argmaxStep]
  split <;> rfl

/-- The scan started from any `some` seed stays defined. -/
theorem argmax_some_isSome (hash : Nat → Nat → Nat) (key : Nat) :
    ∀ (l : List Backend) (a : Backend),
      (l.foldl (argmaxStep hash key) (some a)).isSome := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x rest ih =>
    intro a
    rw [List.foldl_cons, argmaxStep_some]
    exact ih _

/-- The scan of a non-empty list is defined. -/
theorem specRendezvous_isSome {hash : Nat → Nat → Nat} {key : Nat}
    {bs : List Backend} (h : bs ≠ []) : (specRendezvous hash key bs).isSome := by
  cases bs with
  | nil => exact absurd rfl h
  | cons x rest =>
    unfold specRendezvous
    rw [List.foldl_cons]
    have : argmaxStep hash key none x = some x := rfl
    rw [this]
    exact argmax_some_isSome hash key rest x

/-- The scan result is a member of the list (given a `none` seed). -/
theorem argmax_mem (hash : Nat → Nat → Nat) (key : Nat) :
    ∀ (bs : List Backend) (acc : Option Backend) (b : Backend),
      bs.foldl (argmaxStep hash key) acc = some b → b ∈ bs ∨ acc = some b := by
  intro bs
  induction bs with
  | nil =>
    intro acc b h
    rw [List.foldl_nil] at h
    exact Or.inr h
  | cons x rest ih =>
    intro acc b h
    rw [List.foldl_cons] at h
    rcases ih (argmaxStep hash key acc x) b h with hb | hb
    · exact Or.inl (List.mem_cons_of_mem _ hb)
    · cases acc with
      | none =>
        obtain rfl : x = b := by simpa only [argmaxStep, Option.some.injEq] using hb
        exact Or.inl (by simp)
      | some a =>
        by_cases hxa : keyGe (hrwKey hash key x) (hrwKey hash key a) = true
        · have hstep : argmaxStep hash key (some a) x = some x := by
            simp [argmaxStep, hxa]
          rw [hstep, Option.some.injEq] at hb
          subst hb
          exact Or.inl (by simp)
        · have hstep : argmaxStep hash key (some a) x = some a := by
            simp [argmaxStep, hxa]
          rw [hstep] at hb
          exact Or.inr hb

/-- **Argmax invariant.** The scan result's key dominates the seed (if any) and
every list element. This is the "it really is the maximum" content. -/
theorem argmax_invariant (hash : Nat → Nat → Nat) (key : Nat) :
    ∀ (bs : List Backend) (acc : Option Backend) (b : Backend),
      bs.foldl (argmaxStep hash key) acc = some b →
      (∀ a, acc = some a →
        keyGe (hrwKey hash key b) (hrwKey hash key a) = true) ∧
      (∀ c ∈ bs, keyGe (hrwKey hash key b) (hrwKey hash key c) = true) := by
  intro bs
  induction bs with
  | nil =>
    intro acc b h
    rw [List.foldl_nil] at h
    subst h
    refine ⟨fun a ha => ?_, fun c hc => absurd hc (List.not_mem_nil c)⟩
    rw [Option.some.injEq] at ha
    subst ha
    exact keyGe_refl _
  | cons x rest ih =>
    intro acc b h
    rw [List.foldl_cons] at h
    obtain ⟨ihacc, ihmem⟩ := ih (argmaxStep hash key acc x) b h
    cases acc with
    | none =>
      have hbx : keyGe (hrwKey hash key b) (hrwKey hash key x) = true := ihacc x rfl
      refine ⟨fun a ha => by simp at ha, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with hc | hc
      · subst hc; exact hbx
      · exact ihmem c hc
    | some a =>
      by_cases hxa : keyGe (hrwKey hash key x) (hrwKey hash key a) = true
      · have hstep : argmaxStep hash key (some a) x = some x := by
          simp [argmaxStep, hxa]
        have hbx : keyGe (hrwKey hash key b) (hrwKey hash key x) = true :=
          ihacc x hstep
        refine ⟨fun a' ha' => ?_, fun c hc => ?_⟩
        · rw [Option.some.injEq] at ha'; subst ha'
          exact keyGe_trans hbx hxa
        · rcases List.mem_cons.mp hc with hc | hc
          · subst hc; exact hbx
          · exact ihmem c hc
      · have hstep : argmaxStep hash key (some a) x = some a := by
          simp [argmaxStep, hxa]
        have hba : keyGe (hrwKey hash key b) (hrwKey hash key a) = true :=
          ihacc a hstep
        have hax : keyGe (hrwKey hash key a) (hrwKey hash key x) = true :=
          keyGe_total _ _ (by simpa using hxa)
        refine ⟨fun a' ha' => ?_, fun c hc => ?_⟩
        · rw [Option.some.injEq] at ha'; subst ha'; exact hba
        · rcases List.mem_cons.mp hc with hc | hc
          · subst hc; exact keyGe_trans hba hax
          · exact ihmem c hc

/-- A dominating key with a distinct id `beats` (strictly, the implementation's
comparator): the argmax spec's `≥` sharpens to `>` once ids differ. -/
theorem keyGe_to_beats {hash : Nat → Nat → Nat} {key : Nat} {b c : Backend}
    (hcid : c.id ≠ b.id)
    (hge : keyGe (hrwKey hash key b) (hrwKey hash key c) = true) :
    beats hash key b c = true := by
  simp only [keyGe, hrwKey, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hge
  simp only [beats, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **Rendezvous refinement.** The implementation selects exactly the argmax of
the hash score. For candidate lists with distinct ids (the config-loader
invariant `idsNodup`, the same hypothesis the winner-characterization theorems
use), `rendezvous` equals the independent `specRendezvous`. -/
theorem rendezvous_refines_spec {hash : Nat → Nat → Nat} {key : Nat}
    {bs : List Backend} (hnd : idsNodup bs) :
    rendezvous hash key bs = specRendezvous hash key bs := by
  cases bs with
  | nil => rfl
  | cons x rest =>
    obtain ⟨b, hb⟩ :=
      Option.isSome_iff_exists.mp (specRendezvous_isSome (bs := x :: rest) (by simp))
    rw [hb]
    unfold specRendezvous at hb
    have hmem : b ∈ (x :: rest) := by
      rcases argmax_mem hash key (x :: rest) none b hb with h | h
      · exact h
      · simp at h
    have hall : ∀ c ∈ (x :: rest), c.id ≠ b.id → beats hash key b c = true := by
      intro c hc hcid
      exact keyGe_to_beats hcid
        ((argmax_invariant hash key (x :: rest) none b hb).2 c hc)
    exact rendezvous_of_beats_all hnd hmem hall

/-! ## Weighted round-robin: refinement against an interval specification -/

/-- **Independent WRR interval selector.** Walking the candidate list carrying
the ABSOLUTE cumulative-weight offset `acc`, the residue `r` selects the first
backend whose half-open interval `[acc, acc + weight)` contains `r`. This is the
cumulative-interval reading of the schedule, decided by absolute containment —
it never subtracts from `r`. -/
def specPick : List Backend → Nat → Nat → Option Backend
  | [], _, _ => none
  | b :: bs, r, acc =>
    if acc ≤ r ∧ r < acc + b.weight then some b
    else specPick bs r (acc + b.weight)

/-- **Independent WRR specification.** Reduce the round counter modulo the total
weight, then choose by absolute interval containment. `none` exactly when the
total weight is zero. -/
def specWrr (bs : List Backend) (round : Nat) : Option Backend :=
  if totalWeight bs = 0 then none
  else specPick bs (round % totalWeight bs) 0

/-- The implementation's subtractive walk from residue `r - acc` equals the
spec's absolute-interval walk from offset `acc`, whenever `acc ≤ r`. -/
theorem specPick_eq :
    ∀ (bs : List Backend) (acc r : Nat), acc ≤ r →
      pickByResidue bs (r - acc) = specPick bs r acc := by
  intro bs
  induction bs with
  | nil => intro acc r _; rfl
  | cons c rest ih =>
    intro acc r hle
    simp only [pickByResidue, specPick]
    by_cases hlt : r - acc < c.weight
    · rw [if_pos hlt, if_pos ⟨hle, by omega⟩]
    · have hnot : ¬ (acc ≤ r ∧ r < acc + c.weight) := by
        rintro ⟨_, h2⟩; omega
      rw [if_neg hlt, if_neg hnot]
      have hle' : acc + c.weight ≤ r := by omega
      rw [← ih (acc + c.weight) r hle']
      congr 1
      omega

/-- **WRR refinement.** The implementation `wrr` equals the independent
interval specification `specWrr` on every candidate list and round counter. -/
theorem wrr_refines_spec (bs : List Backend) (round : Nat) :
    wrr bs round = specWrr bs round := by
  unfold wrr specWrr
  by_cases h : totalWeight bs = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    have := specPick_eq bs 0 (round % totalWeight bs) (Nat.zero_le _)
    simpa using this

/-! ## Non-vacuity witnesses: argmax / interval diverge from wrong rules -/

/-- HRW is NOT "return the first candidate" and NOT "return the hash-minimum":
with score = id over `[b0, b1]`, the argmax is the tail `b1` (higher score),
while both wrong rules would yield the head `b0`. Any implementation matching
either wrong rule refutes `rendezvous_refines_spec`. -/
example :
    specRendezvous (fun _ i => i) 0
        [⟨0, 1, 0, 0, true, .active⟩, ⟨1, 1, 0, 0, true, .active⟩]
      = some ⟨1, 1, 0, 0, true, .active⟩
    ∧ rendezvous (fun _ i => i) 0
        [⟨0, 1, 0, 0, true, .active⟩, ⟨1, 1, 0, 0, true, .active⟩]
      = some ⟨1, 1, 0, 0, true, .active⟩
    ∧ ([⟨0, 1, 0, 0, true, .active⟩, ⟨1, 1, 0, 0, true, .active⟩] : List Backend).head?
      = some ⟨0, 1, 0, 0, true, .active⟩ := by
  refine ⟨by decide, by decide, by decide⟩

/-- WRR is NOT "always the first candidate": two unit-weight backends split the
two-round cycle, so residue `1` selects `b1`, not the head `b0`. -/
example :
    specWrr [⟨0, 1, 0, 0, true, .active⟩, ⟨1, 1, 0, 0, true, .active⟩] 1
      = some ⟨1, 1, 0, 0, true, .active⟩
    ∧ wrr [⟨0, 1, 0, 0, true, .active⟩, ⟨1, 1, 0, 0, true, .active⟩] 1
      = some ⟨1, 1, 0, 0, true, .active⟩
    ∧ ([⟨0, 1, 0, 0, true, .active⟩, ⟨1, 1, 0, 0, true, .active⟩] : List Backend).head?
      = some ⟨0, 1, 0, 0, true, .active⟩ := by
  refine ⟨by decide, by decide, by decide⟩

end Proxy
