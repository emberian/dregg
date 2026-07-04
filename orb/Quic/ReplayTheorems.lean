import Quic.Replay

/-!
# 0-RTT anti-replay on a sharded server — the theorems

**Headline** (`accepted_at_most_once`): across all shards and all
interleavings of the demonic network — replays of any early-data attempt
to any shard any number of times, crashes, message loss, timeouts — each
ticket's early data is accepted **at most once, globally**.

Proof shape — *single-owner serialization as a token argument*: the mark
`(owner t, t)` in the owner's core-local strike register is the unique
decision token for ticket `t`. Define the budget

    accepts-so-far + strike-acks-in-flight  ≤  struck (0 or 1)

Every move preserves it: a local accept spends the token into an accept;
an owner approval spends it into an in-flight strike-ack; a remote accept
converts one in-flight strike-ack into an accept; everything else leaves
the left side fixed or smaller. Since the register never unmarks, the
budget never exceeds 1 from the initial state (`trace_budget`), and the
bound follows.

Corollaries:
* `owner_decides_at_most_once` — the serialization itself: at most one
  owner decision (`localAccept`/`ownerOk`) per ticket, ever.
* `accept_remote_needs_owner_ok` — the mis-steer path is pinned: every
  remote accept is preceded by the matching owner approval; with the
  above, the mis-steered path preserves at-most-once by construction.
* `owner_gone_declines` — owner dead, ticket undecided, no strike-ack in
  flight ⇒ **no accept ever again**: the only outcome for held early data
  is decline (`timeout` stays enabled — `decline_always_enabled`), i.e.
  fall back to 1-RTT. Owner loss costs latency, never correctness.
-/

namespace Quic.Replay

/-! ## Small facts about the counters -/

theorem struck_le_one (cfg : Cfg) (t : TicketId) (s : St) :
    struck cfg t s ≤ 1 := by
  unfold struck; split <;> omega

theorem struck_init (cfg : Cfg) (t : TicketId) : struck cfg t init = 0 := by
  simp [struck, init]

theorem okWires_init (t : TicketId) : okWires t init = 0 := rfl

/-! ## The budget invariant, one step -/

theorem step_budget {cfg : Cfg} {s s' : St} {l : Lbl}
    (h : Step cfg s l s') (t : TicketId) :
    (if Lbl.isAccept t l then 1 else 0) + struck cfg t s + okWires t s'
      ≤ struck cfg t s' + okWires t s := by
  cases h with
  | @localAccept t' a halive hnew =>
      by_cases ht : t' = t
      · subst ht
        simp [Lbl.isAccept, struck, okWires, hnew]
      · simp [Lbl.isAccept, struck, okWires, ht, Ne.symm ht, Prod.ext_iff]
  | localReject halive hused =>
      simp [Lbl.isAccept]
  | forward hmiss halive =>
      simp [Lbl.isAccept, struck, okWires, Wire.isOk,
        List.countP_append, List.countP_cons]
  | @ownerOk t' sh a w₁ w₂ halive hwire hnew =>
      by_cases ht : t' = t
      · subst ht
        simp [Lbl.isAccept, struck, okWires, hnew, hwire, Wire.isOk,
          List.countP_append, List.countP_cons]
        omega
      · simp [Lbl.isAccept, struck, okWires, ht, Ne.symm ht, Prod.ext_iff,
          hwire, Wire.isOk, List.countP_append, List.countP_cons]
  | @ownerNo t' sh a w₁ w₂ halive hwire hused =>
      simp [Lbl.isAccept, struck, okWires, hwire, Wire.isOk,
        List.countP_append, List.countP_cons]
  | @acceptRemote t' sh a w₁ w₂ halive hwire =>
      by_cases ht : t' = t
      · subst ht
        simp [Lbl.isAccept, struck, okWires, hwire, Wire.isOk,
          List.countP_append, List.countP_cons]
        split <;> omega
      · simp [Lbl.isAccept, struck, okWires, ht, hwire, Wire.isOk,
          List.countP_append, List.countP_cons]
  | @declineRemote t' sh a w₁ w₂ hwire =>
      simp [Lbl.isAccept, struck, okWires, hwire, Wire.isOk,
        List.countP_append, List.countP_cons]
  | timeout =>
      simp [Lbl.isAccept]
  | crash =>
      simp [Lbl.isAccept, struck, okWires]
  | @lose w w₁ w₂ hwire =>
      show (0:Nat) + struck cfg t s + okWires t { s with wires := w₁ ++ w₂ }
        ≤ struck cfg t { s with wires := w₁ ++ w₂ } + okWires t s
      have hst : struck cfg t { s with wires := w₁ ++ w₂ }
          = struck cfg t s := rfl
      have hle : okWires t { s with wires := w₁ ++ w₂ } ≤ okWires t s := by
        simp only [okWires, hwire, List.countP_append, List.countP_cons]
        split <;> omega
      rw [hst]
      omega

/-! ## The budget invariant, whole trace -/

theorem trace_budget {cfg : Cfg} {s s' : St} {ls : List Lbl}
    (tr : Trace cfg s ls s') (t : TicketId) :
    accepts t ls + struck cfg t s + okWires t s'
      ≤ struck cfg t s' + okWires t s := by
  induction ls generalizing s with
  | nil =>
      cases tr
      simp only [accepts, List.countP_nil]
      omega
  | cons l ls ih =>
      cases tr with
      | cons h tr' =>
          have hb := step_budget h t
          have hi := ih tr'
          simp only [accepts, List.countP_cons] at hi ⊢
          cases hl : Lbl.isAccept t l <;> simp [hl] at hb ⊢ <;> omega

/-! ## THE HEADLINE -/

/-- **Global at-most-once.** In every trace of the sharded system from
the initial state — under arbitrary replay of early-data attempts to
arbitrary shards, arbitrary interleavings, crashes, message loss, and
timeouts — each ticket's early data is accepted at most once, counting
accepts across *all* shards and both the correctly-steered and the
mis-steered path. -/
theorem accepted_at_most_once {cfg : Cfg} {s' : St} {ls : List Lbl}
    (tr : Trace cfg init ls s') (t : TicketId) :
    accepts t ls ≤ 1 := by
  have hb := trace_budget tr t
  have h1 := struck_le_one cfg t s'
  have h2 := struck_init cfg t
  have h3 := okWires_init t
  omega

/-! ## Single-owner serialization, explicitly -/

theorem struck_mono {cfg : Cfg} {s s' : St} {l : Lbl}
    (h : Step cfg s l s') (t : TicketId) :
    struck cfg t s ≤ struck cfg t s' := by
  have hsub : ∀ x ∈ s.used, x ∈ s'.used := by
    cases h <;> intro x hx <;>
      first
      | exact hx
      | exact List.mem_cons_of_mem _ hx
  unfold struck
  split
  · next hm => rw [if_pos (hsub _ hm)]; exact Nat.le_refl _
  · exact Nat.zero_le _

theorem step_decision_budget {cfg : Cfg} {s s' : St} {l : Lbl}
    (h : Step cfg s l s') (t : TicketId) :
    (if Lbl.isDecision t l then 1 else 0) + struck cfg t s
      ≤ struck cfg t s' := by
  have hmono := struck_mono h t
  cases h with
  | @localAccept t' a halive hnew =>
      by_cases ht : t' = t
      · subst ht
        simp [Lbl.isDecision, struck, hnew]
      · simp [Lbl.isDecision, ht]
        omega
  | @ownerOk t' sh a w₁ w₂ halive hwire hnew =>
      by_cases ht : t' = t
      · subst ht
        simp [Lbl.isDecision, struck, hnew]
      · rw [show Lbl.isDecision t (.ownerOk t' sh a) = false from
          beq_eq_false_iff_ne.mpr ht]
        simpa using hmono
  | localReject halive hused => simp [Lbl.isDecision]
  | forward hmiss halive => simpa [Lbl.isDecision] using hmono
  | ownerNo halive hwire hused => simpa [Lbl.isDecision] using hmono
  | acceptRemote halive hwire => simpa [Lbl.isDecision] using hmono
  | declineRemote hwire => simpa [Lbl.isDecision] using hmono
  | timeout => simp [Lbl.isDecision]
  | crash => simpa [Lbl.isDecision] using hmono
  | lose hwire => simpa [Lbl.isDecision] using hmono

theorem trace_decisions {cfg : Cfg} {s s' : St} {ls : List Lbl}
    (tr : Trace cfg s ls s') (t : TicketId) :
    decisions t ls + struck cfg t s ≤ struck cfg t s' := by
  induction ls generalizing s with
  | nil =>
      cases tr
      simp only [decisions, List.countP_nil]
      omega
  | cons l ls ih =>
      cases tr with
      | cons h tr' =>
          have hb := step_decision_budget h t
          have hi := ih tr'
          simp only [decisions, List.countP_cons] at hi ⊢
          cases hl : Lbl.isDecision t l <;> simp [hl] at hb ⊢ <;> omega

/-- **Single-owner serialization**: at most one owner decision — one
strike-register write — per ticket, ever, across the whole system. Each
ticket id has exactly one deciding core, and that core decides once. -/
theorem owner_decides_at_most_once {cfg : Cfg} {s' : St} {ls : List Lbl}
    (tr : Trace cfg init ls s') (t : TicketId) :
    decisions t ls ≤ 1 := by
  have hb := trace_decisions tr t
  have h1 := struck_le_one cfg t s'
  have h2 := struck_init cfg t
  omega

/-! ## The mis-steer path is pinned to its owner approval -/

/-- Is this wire the strike-ack for the specific attempt `(t, sh, a)`? -/
def Wire.isAckOf (t : TicketId) (sh : Shard) (a : AttemptId) : Wire → Bool
  | .resp t' sh' a' ok => t' == t && (sh' == sh && (a' == a && ok))
  | _ => false

/-- In-flight strike-acks for the specific attempt `(t, sh, a)`. -/
def ackWires (t : TicketId) (sh : Shard) (a : AttemptId) (s : St) : Nat :=
  s.wires.countP (Wire.isAckOf t sh a)

/-- Cold lemma: only `ownerOk t sh a` can create the strike-ack for
attempt `(t, sh, a)`; every other move preserves its absence. -/
theorem step_ack_cold {cfg : Cfg} {s s' : St} {l : Lbl}
    {t : TicketId} {sh : Shard} {a : AttemptId}
    (h : Step cfg s l s') (h0 : ackWires t sh a s = 0)
    (hl : l ≠ .ownerOk t sh a) :
    ackWires t sh a s' = 0 := by
  cases h with
  | localAccept halive hnew => exact h0
  | localReject halive hused => exact h0
  | @forward t' sh' a' hmiss halive =>
      simp [ackWires, Wire.isAckOf, List.countP_append, List.countP_cons,
        -List.countP_eq_zero] at h0 ⊢
      omega
  | @ownerOk t' sh' a' w₁ w₂ halive hwire hnew =>
      by_cases hcase : t' = t ∧ sh' = sh ∧ a' = a
      · obtain ⟨h1, h2, h3⟩ := hcase
        subst h1; subst h2; subst h3
        exact absurd rfl hl
      · simp [ackWires, Wire.isAckOf, hwire, hcase, List.countP_append,
          List.countP_cons, -List.countP_eq_zero] at h0 ⊢
        omega
  | @ownerNo t' sh' a' w₁ w₂ halive hwire hused =>
      simp [ackWires, Wire.isAckOf, hwire, List.countP_append,
        List.countP_cons, -List.countP_eq_zero] at h0 ⊢
      omega
  | @acceptRemote t' sh' a' w₁ w₂ halive hwire =>
      by_cases hcase : t' = t ∧ sh' = sh ∧ a' = a
      · exfalso
        obtain ⟨h1, h2, h3⟩ := hcase
        subst h1; subst h2; subst h3
        simp [ackWires, Wire.isAckOf, hwire, List.countP_append,
          List.countP_cons, -List.countP_eq_zero] at h0
      · simp [ackWires, Wire.isAckOf, hwire, hcase, List.countP_append,
          List.countP_cons, -List.countP_eq_zero] at h0 ⊢
        omega
  | @declineRemote t' sh' a' w₁ w₂ hwire =>
      simp [ackWires, Wire.isAckOf, hwire, List.countP_append,
        List.countP_cons, -List.countP_eq_zero] at h0 ⊢
      omega
  | timeout => exact h0
  | crash => exact h0
  | @lose w w₁ w₂ hwire =>
      simp [ackWires, hwire, List.countP_append, List.countP_cons,
        -List.countP_eq_zero] at h0 ⊢
      exact ⟨h0.1, h0.2.1⟩

theorem cold_no_remote_accept {cfg : Cfg} {s s' : St}
    {t : TicketId} {sh : Shard} {a : AttemptId} {m rest : List Lbl}
    (tr : Trace cfg s (m ++ .acceptRemote t sh a :: rest) s')
    (h0 : ackWires t sh a s = 0)
    (hm : Lbl.ownerOk t sh a ∉ m) : False := by
  induction m generalizing s with
  | nil =>
      cases tr with
      | cons h _ =>
          cases h with
          | acceptRemote halive hwire =>
              simp [ackWires, Wire.isAckOf, hwire, List.countP_append,
                List.countP_cons, -List.countP_eq_zero] at h0
  | cons l m' ih =>
      cases tr with
      | cons h tr' =>
          have hlne : l ≠ Lbl.ownerOk t sh a := fun he =>
            hm (he ▸ List.mem_cons_self l m')
          have hm' : Lbl.ownerOk t sh a ∉ m' := fun hmem =>
            hm (List.mem_cons_of_mem _ hmem)
          exact ih tr' (step_ack_cold h h0 hlne) hm'

/-- **The mis-steer path preserves the property by construction**: every
remote accept of attempt `(t, sh, a)` — the accept a mis-steered shard
performs on a strike-ack — is preceded by the owner's matching approval
`ownerOk t sh a`. Together with `owner_decides_at_most_once` (approvals
and local accepts share one budget) the mis-steered path cannot introduce
a second acceptance. -/
theorem accept_remote_needs_owner_ok {cfg : Cfg} {s' : St}
    {t : TicketId} {sh : Shard} {a : AttemptId} {m₁ m₂ : List Lbl}
    (tr : Trace cfg init (m₁ ++ .acceptRemote t sh a :: m₂) s') :
    Lbl.ownerOk t sh a ∈ m₁ := by
  refine Classical.byContradiction fun hno => ?_
  exact cold_no_remote_accept tr rfl hno

/-! ## Owner gone ⇒ decline (never a second accept) -/

/-- Frozen-owner step lemma: with the owner dead, the ticket undecided,
and no strike-ack in flight, no move accepts `t`, and all three facts
persist. -/
theorem step_dead_frozen {cfg : Cfg} {s s' : St} {l : Lbl}
    (h : Step cfg s l s') (t : TicketId)
    (hd : cfg.owner t ∈ s.dead)
    (hu : (cfg.owner t, t) ∉ s.used)
    (hw : okWires t s = 0) :
    Lbl.isAccept t l = false ∧ cfg.owner t ∈ s'.dead ∧
      (cfg.owner t, t) ∉ s'.used ∧ okWires t s' = 0 := by
  cases h with
  | @localAccept t' a halive hnew =>
      by_cases ht : t' = t
      · subst ht; exact absurd hd halive
      · refine ⟨beq_eq_false_iff_ne.mpr ht, hd, ?_, hw⟩
        intro hmem
        rcases List.mem_cons.mp hmem with he | he
        · exact ht (congrArg Prod.snd he).symm
        · exact hu he
  | localReject halive hused => exact ⟨rfl, hd, hu, hw⟩
  | @forward t' sh' a' hmiss halive =>
      refine ⟨rfl, hd, hu, ?_⟩
      simp [okWires, Wire.isOk, List.countP_append, List.countP_cons,
        -List.countP_eq_zero] at hw ⊢
      omega
  | @ownerOk t' sh' a' w₁ w₂ halive hwire hnew =>
      by_cases ht : t' = t
      · subst ht; exact absurd hd halive
      · refine ⟨rfl, hd, ?_, ?_⟩
        · intro hmem
          rcases List.mem_cons.mp hmem with he | he
          · exact ht (congrArg Prod.snd he).symm
          · exact hu he
        · simp [okWires, Wire.isOk, hwire, ht, List.countP_append,
            List.countP_cons, -List.countP_eq_zero] at hw ⊢
          omega
  | @ownerNo t' sh' a' w₁ w₂ halive hwire hused =>
      refine ⟨rfl, hd, hu, ?_⟩
      simp [okWires, Wire.isOk, hwire, List.countP_append,
        List.countP_cons, -List.countP_eq_zero] at hw ⊢
      omega
  | @acceptRemote t' sh' a' w₁ w₂ halive hwire =>
      by_cases ht : t' = t
      · subst ht
        exfalso
        simp [okWires, Wire.isOk, hwire, List.countP_append,
          List.countP_cons, -List.countP_eq_zero] at hw
      · refine ⟨beq_eq_false_iff_ne.mpr ht, hd, hu, ?_⟩
        simp [okWires, Wire.isOk, hwire, ht, List.countP_append,
          List.countP_cons, -List.countP_eq_zero] at hw ⊢
        omega
  | @declineRemote t' sh' a' w₁ w₂ hwire =>
      refine ⟨rfl, hd, hu, ?_⟩
      simp [okWires, Wire.isOk, hwire, List.countP_append,
        List.countP_cons, -List.countP_eq_zero] at hw ⊢
      omega
  | timeout => exact ⟨rfl, hd, hu, hw⟩
  | crash => exact ⟨rfl, List.mem_cons_of_mem _ hd, hu, hw⟩
  | @lose w w₁ w₂ hwire =>
      refine ⟨rfl, hd, hu, ?_⟩
      simp [okWires, hwire, List.countP_append, List.countP_cons,
        -List.countP_eq_zero] at hw ⊢
      exact ⟨hw.1, hw.2.1⟩

/-- **Owner gone ⇒ decline.** Once the owner shard of ticket `t` is dead
with `t` undecided and no strike-ack in flight, no continuation of the
system accepts `t`'s early data — the only possible outcome for any held
or replayed attempt is decline / fall back to 1-RTT. Owner loss is a
latency cost, never a correctness loss. -/
theorem owner_gone_declines {cfg : Cfg} {s s' : St} {ls : List Lbl}
    {t : TicketId}
    (tr : Trace cfg s ls s')
    (hd : cfg.owner t ∈ s.dead)
    (hu : (cfg.owner t, t) ∉ s.used)
    (hw : okWires t s = 0) :
    accepts t ls = 0 := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih =>
      cases tr with
      | cons h tr' =>
          obtain ⟨hacc, hd', hu', hw'⟩ := step_dead_frozen h t hd hu hw
          have hrec := ih tr' hd' hu' hw'
          simp only [accepts, List.countP_cons] at hrec ⊢
          simp [hacc, hrec]

/-- The 1-RTT fallback is always available: a requester may decline any
held attempt at any time (timeout). Progress is never hostage to the
owner-check. -/
theorem decline_always_enabled (cfg : Cfg) (s : St)
    (t : TicketId) (sh : Shard) (a : AttemptId) :
    Step cfg s (.timeout t sh a) s :=
  Step.timeout

/-! ## Non-vacuity: both accept paths are live -/

/-- Sanity: the correctly-steered accept is reachable. -/
example : Trace ⟨fun _ => 0⟩ init [.localAccept 7 0]
      { init with used := [(0, 7)] } ∧
    accepts 7 [.localAccept 7 0] = 1 :=
  ⟨.cons (.localAccept (by simp [init]) (by simp [init])) .nil, rfl⟩

/-- Sanity: the mis-steered path (forward → owner approval → remote
accept) is reachable and accepts exactly once. -/
example :
    ∃ s', Trace ⟨fun _ => 0⟩ init
      [.forward 7 1 0, .ownerOk 7 1 0, .acceptRemote 7 1 0] s' ∧
    accepts 7 [.forward 7 1 0, .ownerOk 7 1 0, .acceptRemote 7 1 0] = 1 := by
  refine ⟨_, .cons (.forward (by decide) (by simp [init]))
    (.cons (.ownerOk (w₁ := []) (w₂ := []) (by simp [init]) rfl (by simp [init]))
      (.cons (.acceptRemote (w₁ := []) (w₂ := []) (by simp [init]) rfl)
        .nil)), rfl⟩

end Quic.Replay
