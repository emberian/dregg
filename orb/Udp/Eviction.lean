/-
Udp.Eviction — idle-timeout eviction is deadline-honored (theorem 3).

The idle sweep is a filter on the activity clock: it keeps exactly the sessions
still inside their window (`now < lastActive + timeout`) and drops the rest. All
statements quantify over the explicit time input `now`, so they hold for every
clock behavior.

  * `mem_sweep_iff` — the exact survival criterion.
  * `sweep_survives` / `no_early_eviction` — a session with idle `< timeout` is
    **never** evicted: it survives with binding and identity intact.
  * `sweep_evicts` — a session with idle `≥ timeout` is removed.
  * `evicted_implies_idle_ge_timeout` — **the deadline guarantee**: if a session
    is gone after a sweep, its idle gap had reached `timeout`. Eviction happens
    only on or after the deadline, never before.
  * `evict_then_reopen_fresh` — after an expired session is swept, the next
    datagram from that client opens a *fresh* session on a **new** binding
    (`> ` the evicted one): no stale binding is ever reused.
-/

import Udp.Session

namespace Udp

/-- Exact survival criterion for the idle sweep: an entry is retained iff it was
present and still inside its idle window (`now < lastActive + timeout`). -/
theorem mem_sweep_iff {timeout now : Nat} {r : Relay} {q : Addr × Session} :
    q ∈ (sweep timeout now r).sessions ↔
      q ∈ r.sessions ∧ now < q.2.lastActive + timeout := by
  simp only [sweep, List.mem_filter, decide_eq_true_eq]

/-- The sweep leaves `nextBinding` untouched (it only shrinks the table). -/
@[simp] theorem sweep_nextBinding {timeout now : Nat} {r : Relay} :
    (sweep timeout now r).nextBinding = r.nextBinding := rfl

/-- **No early eviction.** A session whose idle gap is still below the timeout
(`now < lastActive + timeout`) survives the sweep with its exact session state
(binding included). Under key-uniqueness the surviving lookup is that same
session. -/
theorem sweep_survives {timeout now : Nat} {r : Relay} {a : Addr} {s : Session}
    (hk : KeyUnique r.sessions) (h : lookup r.sessions a = some s)
    (hlt : now < s.lastActive + timeout) :
    lookup (sweep timeout now r).sessions a = some s := by
  have hmem : (a, s) ∈ r.sessions := lookup_mem h
  have hmem' : (a, s) ∈ (sweep timeout now r).sessions :=
    mem_sweep_iff.mpr ⟨hmem, hlt⟩
  exact mem_lookup (sweep_keyUnique timeout now r hk) hmem'

/-- Restatement of no-early-eviction as a live-session guarantee: while idle
`< timeout`, the client still has its session after the sweep. -/
theorem no_early_eviction {timeout now : Nat} {r : Relay} {a : Addr} {s : Session}
    (hk : KeyUnique r.sessions) (h : lookup r.sessions a = some s)
    (hlt : now < s.lastActive + timeout) :
    lookup (sweep timeout now r).sessions a ≠ none := by
  rw [sweep_survives hk h hlt]; simp

/-- **Eviction on deadline.** A session whose idle gap has reached the timeout
(`lastActive + timeout ≤ now`) is removed by the sweep. -/
theorem sweep_evicts {timeout now : Nat} {r : Relay} {a : Addr} {s : Session}
    (hk : KeyUnique r.sessions) (h : lookup r.sessions a = some s)
    (hexp : s.lastActive + timeout ≤ now) :
    lookup (sweep timeout now r).sessions a = none := by
  cases hsw : lookup (sweep timeout now r).sessions a with
  | none => rfl
  | some s' =>
    exfalso
    have hmem' : (a, s') ∈ (sweep timeout now r).sessions := lookup_mem hsw
    obtain ⟨hmem, hlt⟩ := mem_sweep_iff.mp hmem'
    have hlt2 : now < s'.lastActive + timeout := hlt
    -- s' survived, so its idle < timeout; but under key-uniqueness s' = s (expired)
    have hss : s = s' := lookup_unique hk (lookup_mem h) hmem
    rw [← hss] at hlt2
    omega

/-- **The deadline guarantee (theorem 3).** A session is evicted only after its
idle gap reaches the timeout: if `a` had a session that is gone after the sweep,
then `idle ≥ timeout` (`lastActive + timeout ≤ now`). Contrapositive of
`sweep_survives`. -/
theorem evicted_implies_idle_ge_timeout {timeout now : Nat} {r : Relay} {a : Addr}
    {s : Session} (hk : KeyUnique r.sessions) (h : lookup r.sessions a = some s)
    (hev : lookup (sweep timeout now r).sessions a = none) :
    s.lastActive + timeout ≤ now := by
  rcases Nat.lt_or_ge now (s.lastActive + timeout) with hlt | hge
  · -- still inside the window ⇒ survives, contradicting the eviction
    rw [sweep_survives hk h hlt] at hev
    simp at hev
  · exact hge

/-- **Fresh reopen after eviction — no stale binding reuse (theorem 3).** After
an expired session is swept away, the client's session lookup is empty, and its
*next* datagram opens a fresh session on a newly allocated binding. That fresh
binding is strictly greater than — hence never equal to — the evicted binding:
the evicted upstream binding is never reused. -/
theorem evict_then_reopen_fresh {timeout now now' : Nat} {r : Relay} {a : Addr}
    {p : Payload} {sOld : Session} (hinv : r.Inv)
    (hpre : lookup r.sessions a = some sOld)
    (hexp : sOld.lastActive + timeout ≤ now) :
    lookup (sweep timeout now r).sessions a = none ∧
    (onClient (sweep timeout now r) a p now').2
      = Out.forward a (sweep timeout now r).nextBinding p ∧
    sOld.binding < (sweep timeout now r).nextBinding ∧
    (sweep timeout now r).nextBinding ≠ sOld.binding := by
  have hgone : lookup (sweep timeout now r).sessions a = none :=
    sweep_evicts hinv.keyUnique hpre hexp
  have hdom : sOld.binding < r.nextBinding := hinv.dominated (a, sOld) (lookup_mem hpre)
  refine ⟨hgone, onClient_fresh_forward hgone, ?_, ?_⟩
  · rw [sweep_nextBinding]; exact hdom
  · rw [sweep_nextBinding]; omega

end Udp
