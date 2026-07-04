import Quic.Replay

/-!
# Anti-replay acceptance — CORRECTNESS of the receive decision

`Quic.ReplayTheorems` proves SAFETY-flavoured facts about the anti-replay
machine of `Quic.Replay`: across all shards and all interleavings each
identity's early data is accepted *at most once* (`accepted_at_most_once`),
and the owner decides at most once (`owner_decides_at_most_once`). Those pin
down that the machine never accepts *too much*. On their own they do not say
the machine accepts *exactly* what an anti-replay receiver is required to
accept — a machine that rejected **every** arrival would satisfy at-most-once
vacuously.

This file closes that gap for the home-path decision. It states, *without any
reference to* the implementation state (`St`, the `used` register, `Step`),
the acceptance rule an AEAD anti-replay receiver must implement, and proves the
real transition system realizes it on every reachable state.

## The rule (RFC 9001 §6.2)

RFC 9001 §6.2 (AEAD usage) requires that an endpoint *"remembers which packets
it has already received"* and *"discards packets that it has already
received"*: a received AEAD-protected object is admitted for processing the
first time its packet number / identity appears, and every later duplicate
that is at or below the recorded window is discarded. Collapsed to the
decision that matters — accept-or-discard — the rule is:

> An arriving protected object bearing identity `t` is **ACCEPTED** iff no
> prior acceptance decision for `t` has been recorded; an identity for which a
> decision already exists (a duplicate / replay) is **REJECTED**.

The independent oracle `specAccepts` below is exactly this predicate, defined
over the observable history of *decision events* — the transition alphabet, not
the machine's internal register. `Decides`/`priorDecisions` classify that
history from scratch.

## The refinement

`localAccept_refines_spec` proves the biconditional: at any reachable state
whose home authority for `t` is live, the implementation's home accept
(`Step … (.localAccept t a)`) is enabled **iff** the oracle says accept.
`localReject_refines_spec` proves the dual for the discard step. The bridge is
`used_iff_decided`: the internal register faithfully records the decision
history — `(owner t, t) ∈ used ⟺ a decision for t has occurred`.

## Non-vacuity

The two named corollaries are precisely the failure modes the refinement rules
out:

* `no_duplicate_home_accept` — at a live state whose oracle verdict is REJECT,
  the home accept is **not** enabled. An implementation that admitted a
  duplicate here contradicts the refinement.
* `fresh_home_accept` — at a live state whose oracle verdict is ACCEPT, the
  home accept **is** enabled. An implementation that discarded a fresh arrival
  here contradicts the refinement.

The closing `example`s exhibit both: a fresh identity is accepted from the
initial state, and after one decision the *same* identity's home accept is no
longer enabled while the oracle now rejects it.

The RFC's *window* — remembering only a bounded suffix of packet numbers — is a
memory optimisation over this rule: below the window floor everything is
discarded, so a bounded register that never evicts (as here) is the exact,
window-of-unbounded-extent instance of the same acceptance predicate.
-/

namespace Quic.ReplayCorrect

open Quic.Replay

/-! ## The independent acceptance oracle -/

/-- Does label `l` record a **first-time acceptance decision** for identity
`t`? By the anti-replay rule the decision is the event at which the receiver
commits to having handled `t` — whether admitted directly on its home path
(`localAccept`) or admitted by the home authority on behalf of a mis-delivered
copy (`ownerOk`). Defined purely on the observable transition alphabet. -/
def Decides (t : TicketId) : Lbl → Bool
  | .localAccept t' _ => t' == t
  | .ownerOk t' _ _   => t' == t
  | _ => false

/-- The number of prior acceptance decisions for `t` recorded in history `ls`.
This is the receiver's *memory* stated over observable events, with no
reference to the machine's `used` register. -/
def priorDecisions (t : TicketId) (ls : List Lbl) : Nat :=
  ls.countP (Decides t)

/-- **Anti-replay acceptance oracle** (RFC 9001 §6.2), independent of the
implementation. Given the observable history `ls` of prior decisions, a newly
arriving protected object bearing identity `t` is ACCEPTED iff no prior
decision for `t` exists — the first arrival to reach a decision is admitted,
every later duplicate is discarded. -/
def specAccepts (t : TicketId) (ls : List Lbl) : Prop :=
  priorDecisions t ls = 0

/-! ## The bridge: the register faithfully records the decision history -/

/-- One step changes membership of the mark `(owner t, t)` exactly by whether
the step was a decision for `t`: the mark is present afterwards iff it was
present before or the step decided `t`. The register grows by exactly the
decision events and nothing else. -/
theorem step_used_decides {cfg : Cfg} {s s' : St} {l : Lbl}
    (h : Step cfg s l s') (t : TicketId) :
    ((cfg.owner t, t) ∈ s'.used)
      ↔ ((cfg.owner t, t) ∈ s.used ∨ Decides t l = true) := by
  cases h with
  | @localAccept t' a halive hnew =>
      by_cases ht : t' = t
      · subst ht; simp [Decides, List.mem_cons]
      · have hpair : (cfg.owner t, t) ≠ (cfg.owner t', t') := by
          intro he; exact ht (congrArg Prod.snd he).symm
        simp [Decides, List.mem_cons, hpair, ht, beq_eq_false_iff_ne, Ne.symm ht]
  | @ownerOk t' sh a w₁ w₂ halive hwire hnew =>
      by_cases ht : t' = t
      · subst ht; simp [Decides, List.mem_cons]
      · have hpair : (cfg.owner t, t) ≠ (cfg.owner t', t') := by
          intro he; exact ht (congrArg Prod.snd he).symm
        simp [Decides, List.mem_cons, hpair, ht, beq_eq_false_iff_ne, Ne.symm ht]
  | localReject halive hused => simp [Decides]
  | forward hmiss halive => simp [Decides]
  | ownerNo halive hwire hused => simp [Decides]
  | acceptRemote halive hwire => simp [Decides]
  | declineRemote hwire => simp [Decides]
  | timeout => simp [Decides]
  | crash => simp [Decides]
  | lose hwire => simp [Decides]

/-- Accumulated bridge along a trace: if the mark tracks the decision count `n`
at the start, it tracks `n` plus the decisions of the trace at the end. -/
theorem used_iff_priorDecisions_gen {cfg : Cfg} {s s' : St} {ls : List Lbl}
    (tr : Trace cfg s ls s') (t : TicketId) :
    ∀ n, (((cfg.owner t, t) ∈ s.used) ↔ 0 < n) →
      (((cfg.owner t, t) ∈ s'.used) ↔ 0 < n + priorDecisions t ls) := by
  induction tr with
  | nil => intro n h0; simpa [priorDecisions] using h0
  | @cons sa sb sc l ls hstep tr' ih =>
      intro n h0
      have hd := step_used_decides hstep t
      have h1 : ((cfg.owner t, t) ∈ sb.used)
          ↔ 0 < n + (if Decides t l then 1 else 0) := by
        rw [hd]
        by_cases hb : Decides t l = true
        · simp [hb]
        · simp only [hb, Bool.false_eq_true, or_false, if_false, Nat.add_zero]
          exact h0
      have hstep2 := ih (n + (if Decides t l then 1 else 0)) h1
      have hcnt : priorDecisions t (l :: ls)
          = (if Decides t l then 1 else 0) + priorDecisions t ls := by
        simp [priorDecisions, List.countP_cons, Nat.add_comm]
      rw [hcnt]
      rw [show n + ((if Decides t l then 1 else 0) + priorDecisions t ls)
          = (n + (if Decides t l then 1 else 0)) + priorDecisions t ls by
        omega]
      exact hstep2

/-- **The bridge, from the initial state.** On every reachable state the mark
`(owner t, t)` is in the register iff a decision for `t` has occurred in the
history that produced the state. The internal register is a faithful record of
the observable decision history — neither more nor less. -/
theorem used_iff_decided {cfg : Cfg} {s : St} {ls : List Lbl}
    (tr : Trace cfg init ls s) (t : TicketId) :
    ((cfg.owner t, t) ∈ s.used) ↔ 0 < priorDecisions t ls := by
  have h := used_iff_priorDecisions_gen tr t 0 (by simp [init])
  simpa using h

/-! ## Enabling of the home decisions, characterised by the guards -/

/-- The home accept is enabled exactly under its two guards: the home
authority is live and the identity is unmarked. -/
theorem localAccept_enabled_iff {cfg : Cfg} {s : St} {t : TicketId}
    {a : AttemptId} :
    (∃ s', Step cfg s (.localAccept t a) s')
      ↔ (cfg.owner t ∉ s.dead ∧ (cfg.owner t, t) ∉ s.used) := by
  constructor
  · rintro ⟨s', hstep⟩
    cases hstep with
    | localAccept halive hnew => exact ⟨halive, hnew⟩
  · rintro ⟨halive, hnew⟩
    exact ⟨_, Step.localAccept halive hnew⟩

/-- The home discard is enabled exactly under its two guards: the home
authority is live and the identity is already marked. -/
theorem localReject_enabled_iff {cfg : Cfg} {s : St} {t : TicketId}
    {a : AttemptId} :
    (∃ s', Step cfg s (.localReject t a) s')
      ↔ (cfg.owner t ∉ s.dead ∧ (cfg.owner t, t) ∈ s.used) := by
  constructor
  · rintro ⟨s', hstep⟩
    cases hstep with
    | localReject halive hused => exact ⟨halive, hused⟩
  · rintro ⟨halive, hused⟩
    exact ⟨_, Step.localReject halive hused⟩

/-! ## The refinement -/

/-- **REFINEMENT (accept).** At every reachable state whose home authority for
`t` is live, the implementation's home accept `Step … (.localAccept t a)` is
enabled **iff** the independent oracle accepts (no prior decision for `t`). The
machine admits exactly the arrivals the anti-replay rule admits. -/
theorem localAccept_refines_spec {cfg : Cfg} {s : St} {ls : List Lbl}
    (tr : Trace cfg init ls s) (t : TicketId) (a : AttemptId)
    (halive : cfg.owner t ∉ s.dead) :
    (∃ s', Step cfg s (.localAccept t a) s') ↔ specAccepts t ls := by
  rw [localAccept_enabled_iff]
  have key := used_iff_decided tr t
  unfold specAccepts
  constructor
  · rintro ⟨_, hnew⟩
    have hn : ¬ (0 < priorDecisions t ls) := fun hpos => hnew (key.mpr hpos)
    omega
  · intro hspec
    refine ⟨halive, fun hmem => ?_⟩
    have := key.mp hmem
    omega

/-- **REFINEMENT (discard).** Dually, the home discard `Step … (.localReject t
a)` is enabled at a live state **iff** the oracle rejects (a prior decision for
`t` exists — a duplicate / replay). -/
theorem localReject_refines_spec {cfg : Cfg} {s : St} {ls : List Lbl}
    (tr : Trace cfg init ls s) (t : TicketId) (a : AttemptId)
    (halive : cfg.owner t ∉ s.dead) :
    (∃ s', Step cfg s (.localReject t a) s') ↔ ¬ specAccepts t ls := by
  rw [localReject_enabled_iff]
  have key := used_iff_decided tr t
  unfold specAccepts
  constructor
  · rintro ⟨_, hmem⟩
    have := key.mp hmem
    omega
  · intro hspec
    have hpos : 0 < priorDecisions t ls := by omega
    exact ⟨halive, key.mpr hpos⟩

/-- At a live home authority the two decisions are exactly complementary and
each equals the oracle verdict: accept enabled ⟺ oracle accepts, discard
enabled ⟺ oracle rejects. The receiver is deterministic and faithful. -/
theorem live_decision_is_spec {cfg : Cfg} {s : St} {ls : List Lbl}
    (tr : Trace cfg init ls s) (t : TicketId) (a : AttemptId)
    (halive : cfg.owner t ∉ s.dead) :
    ((∃ s', Step cfg s (.localAccept t a) s') ↔ specAccepts t ls)
      ∧ ((∃ s', Step cfg s (.localReject t a) s') ↔ ¬ specAccepts t ls) :=
  ⟨localAccept_refines_spec tr t a halive,
   localReject_refines_spec tr t a halive⟩

/-! ## Non-vacuity: the two failure modes are ruled out -/

/-- **A duplicate is never admitted.** At a reachable live state whose oracle
verdict is REJECT, the home accept is not enabled. An implementation that
admitted a duplicate here would contradict `localAccept_refines_spec`. -/
theorem no_duplicate_home_accept {cfg : Cfg} {s : St} {ls : List Lbl}
    (tr : Trace cfg init ls s) (t : TicketId) (a : AttemptId)
    (halive : cfg.owner t ∉ s.dead) (hdup : ¬ specAccepts t ls) :
    ¬ ∃ s', Step cfg s (.localAccept t a) s' :=
  fun h => hdup ((localAccept_refines_spec tr t a halive).mp h)

/-- **A fresh arrival is always admitted.** At a reachable live state whose
oracle verdict is ACCEPT, the home accept is enabled. An implementation that
discarded a fresh arrival here would contradict `localAccept_refines_spec`. -/
theorem fresh_home_accept {cfg : Cfg} {s : St} {ls : List Lbl}
    (tr : Trace cfg init ls s) (t : TicketId) (a : AttemptId)
    (halive : cfg.owner t ∉ s.dead) (hfresh : specAccepts t ls) :
    ∃ s', Step cfg s (.localAccept t a) s' :=
  (localAccept_refines_spec tr t a halive).mpr hfresh

/-! ## Concrete witnesses -/

/-- The oracle accepts a fresh identity from the empty history. -/
example : specAccepts 7 ([] : List Lbl) := rfl

/-- A fresh identity is admitted from the initial state (single-owner cfg). -/
example : ∃ s', Step (⟨fun _ => 0⟩ : Cfg) init (.localAccept 7 0) s' :=
  fresh_home_accept .nil 7 0 (by simp [init]) rfl

/-- One decision reaches a state carrying the mark. -/
example : Trace (⟨fun _ => 0⟩ : Cfg) init [.localAccept 7 0]
    { init with used := [(0, 7)] } :=
  .cons (.localAccept (by simp [init]) (by simp [init])) .nil

/-- After one decision the oracle REJECTS the same identity: it is a duplicate. -/
example : ¬ specAccepts 7 [.localAccept 7 0] := by
  simp [specAccepts, priorDecisions, Decides]

/-- And the implementation's home accept for that identity is no longer enabled
— the duplicate is discarded, exactly as the oracle demands. -/
example : ¬ ∃ s', Step (⟨fun _ => 0⟩ : Cfg) { init with used := [(0, 7)] }
    (.localAccept 7 0) s' :=
  no_duplicate_home_accept
    (ls := [.localAccept 7 0])
    (.cons (.localAccept (a := 0) (by simp [init]) (by simp [init])) .nil)
    7 0 (by simp [init]) (by simp [specAccepts, priorDecisions, Decides])

end Quic.ReplayCorrect
