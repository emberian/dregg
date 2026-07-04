/-
Sticky.Routing — the affinity invariants of a stickiness table.

Three properties, over the `route`/`chosen` machine of `Sticky.Basic`:

  * `sticky_stability` / `sticky_stability_fixpoint` / `sticky_stability_idem` —
    a key keeps its backend, and the table is left untouched, for as long as the
    pinned backend stays eligible. Re-routing is then a fixed point: the pin is
    self-reinforcing while it lives.

  * `failover_repin` / `failover_repin_winner` — when the pinned backend leaves
    the eligible set the pin is dead, so the key re-computes deterministically:
    the new choice (and new pin) is exactly the rendezvous winner of the current
    set — a function of `(hash, eligible-set, key)` alone, independent of which
    backend departed.

  * `sticky_minimal_disruption` — the master disruption bound. Shrink the
    eligible set arbitrarily; every key whose *chosen* backend survived keeps
    exactly that backend (live pins and unpinned winners alike). Its
    contrapositive, `failover_only_departed_move`, is the minimal-disruption
    statement for failover: a key moves only if the backend it was using
    (pinned to, or hashing to) left the set — no other key is disturbed.

`failover_isolation` specializes the master bound to a single removal
(`removeBackend d`): every key not using `d` is undisturbed.
-/

import Sticky.Basic

namespace Sticky

open Proxy

/-! ### Stability: a live pin is honoured and self-reinforcing -/

/-- **Sticky stability (step).** A key pinned to a backend that is still eligible
routes to exactly that backend, and the table is returned unchanged. -/
theorem sticky_stability {hash : Nat → Nat → Nat} {bs : List Backend} {t : Table}
    {k bid : Nat} {b : Backend}
    (hnd : idsNodup bs) (hpin : t k = some bid) (hmem : b ∈ bs) (hid : b.id = bid) :
    route hash bs t k = (t, some b) := by
  have hp : pinned bs t k = some b :=
    pinned_of_lookup hpin (lookupId_eq_some_of_mem hnd hmem hid)
  simp only [route, hp]

/-- The chosen backend of a live pin is the pinned backend. -/
theorem sticky_stability_chosen {hash : Nat → Nat → Nat} {bs : List Backend}
    {t : Table} {k bid : Nat} {b : Backend}
    (hnd : idsNodup bs) (hpin : t k = some bid) (hmem : b ∈ bs) (hid : b.id = bid) :
    chosen hash bs t k = some b :=
  chosen_of_pin (pinned_of_lookup hpin (lookupId_eq_some_of_mem hnd hmem hid))

/-- **Sticky stability (table).** A live pin leaves the table untouched — no
re-pin is written. -/
theorem sticky_stability_fixpoint {hash : Nat → Nat → Nat} {bs : List Backend}
    {t : Table} {k bid : Nat} {b : Backend}
    (hnd : idsNodup bs) (hpin : t k = some bid) (hmem : b ∈ bs) (hid : b.id = bid) :
    (route hash bs t k).1 = t := by
  rw [sticky_stability hnd hpin hmem hid]

/-- **Sticky stability (fixed point).** Re-routing a live-pinned key over the
same eligible set reproduces the identical `(table, backend)` — the pin is a
fixed point of `route` while its backend stays eligible. -/
theorem sticky_stability_idem {hash : Nat → Nat → Nat} {bs : List Backend}
    {t : Table} {k bid : Nat} {b : Backend}
    (hnd : idsNodup bs) (hpin : t k = some bid) (hmem : b ∈ bs) (hid : b.id = bid) :
    route hash bs (route hash bs t k).1 k = route hash bs t k := by
  have h := sticky_stability (hash := hash) hnd hpin hmem hid
  rw [h]; exact h

/-! ### Failover: a dead pin re-pins deterministically -/

/-- **Sticky failover (deterministic re-selection).** When the pinned backend has
left the eligible set (its id is absent), the pin is dead and the observed choice
collapses to the stateless rendezvous winner of the current set — a function of
`(hash, bs, k)` alone, independent of which backend departed. -/
theorem failover_chosen {hash : Nat → Nat → Nat} {bs : List Backend} {t : Table}
    {k bid : Nat} (hpin : t k = some bid) (habsent : bid ∉ bs.map Backend.id) :
    chosen hash bs t k = rendezvous hash k bs :=
  chosen_of_no_pin (pinned_none_of_dead hpin (lookupId_eq_none_iff.mpr habsent))

/-- **Sticky failover (re-pin).** In the common nonempty case, the dead-pin key
re-pins to exactly the rendezvous winner `b`, recording `b.id` as its new pin. -/
theorem failover_repin_winner {hash : Nat → Nat → Nat} {bs : List Backend}
    {t : Table} {k bid : Nat} {b : Backend}
    (hpin : t k = some bid) (habsent : bid ∉ bs.map Backend.id)
    (hwin : rendezvous hash k bs = some b) :
    route hash bs t k = (update t k b.id, some b) := by
  have hp : pinned bs t k = none :=
    pinned_none_of_dead hpin (lookupId_eq_none_iff.mpr habsent)
  simp only [route, hp, hwin]

/-- **Sticky failover (empty).** A dead pin over an empty eligible set selects
nothing and writes no pin. -/
theorem failover_repin_empty {hash : Nat → Nat → Nat} {bs : List Backend}
    {t : Table} {k bid : Nat}
    (hpin : t k = some bid) (habsent : bid ∉ bs.map Backend.id)
    (hwin : rendezvous hash k bs = none) :
    route hash bs t k = (t, none) := by
  have hp : pinned bs t k = none :=
    pinned_none_of_dead hpin (lookupId_eq_none_iff.mpr habsent)
  simp only [route, hp, hwin]

/-! ### The master disruption bound -/

/-- **Sticky minimal disruption.** Shrink the eligible set from `bs` to any
subset `bs'`. If the backend a key was routed to under `bs` is still present in
`bs'`, the key routes to exactly that backend under `bs'`. This is uniform over
live pins (the pin stays live) and unpinned keys (the rendezvous winner survives,
by `rendezvous_minimal_disruption`). Note the same table `t` drives both sides:
the invariant is about the routing *decision*, not the bookkeeping. -/
theorem sticky_minimal_disruption {hash : Nat → Nat → Nat} {bs bs' : List Backend}
    {t : Table} {k : Nat} {b : Backend}
    (hnd : idsNodup bs) (hnd' : idsNodup bs')
    (hsub : ∀ c ∈ bs', c ∈ bs)
    (hchosen : chosen hash bs t k = some b) (hb' : b ∈ bs') :
    chosen hash bs' t k = some b := by
  cases htk : t k with
  | none =>
    rw [chosen_of_no_pin (pinned_none_of_unpinned htk)] at hchosen
    rw [chosen_of_no_pin (pinned_none_of_unpinned htk)]
    exact rendezvous_minimal_disruption hnd hnd' hsub hchosen hb'
  | some bid =>
    cases hl : lookupId bid bs with
    | some pb =>
      rw [chosen_of_pin (pinned_of_lookup htk hl)] at hchosen
      have hpb : pb = b := Option.some.inj hchosen
      subst hpb
      have hid : pb.id = bid := lookupId_id hl
      exact chosen_of_pin (pinned_of_lookup htk (lookupId_eq_some_of_mem hnd' hb' hid))
    | none =>
      rw [chosen_of_no_pin (pinned_none_of_dead htk hl)] at hchosen
      have hnm : bid ∉ bs.map Backend.id := lookupId_eq_none_iff.mp hl
      have hnm' : bid ∉ bs'.map Backend.id := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨x, hx, hxid⟩
        exact hnm (List.mem_map.mpr ⟨x, hsub x hx, hxid⟩)
      rw [chosen_of_no_pin (pinned_none_of_dead htk (lookupId_eq_none_iff.mpr hnm'))]
      exact rendezvous_minimal_disruption hnd hnd' hsub hchosen hb'

/-! ### Failover isolation (single removal) -/

/-- **Failover isolation.** Remove one backend `d` from the eligible set. Every
key whose chosen backend was *not* `d` (id-distinct) is undisturbed: it routes to
the same backend as before. -/
theorem failover_isolation {hash : Nat → Nat → Nat} {bs : List Backend} {t : Table}
    {k : Nat} {d b : Backend}
    (hnd : idsNodup bs) (hchosen : chosen hash bs t k = some b) (hne : b.id ≠ d.id) :
    chosen hash (removeBackend d bs) t k = some b :=
  sticky_minimal_disruption hnd (removeBackend_nodup hnd) removeBackend_subset
    hchosen (mem_removeBackend.mpr ⟨chosen_mem hchosen, hne⟩)

/-- **Only the departed backend's keys move.** The contrapositive of isolation:
if removing `d` changes a key's routing, then the key was using `d` — its chosen
backend under `bs` carried `d`'s id (it was pinned to, or hashing to, `d`). No
key that was not using `d` is disturbed. -/
theorem failover_only_departed_move {hash : Nat → Nat → Nat} {bs : List Backend}
    {t : Table} {k : Nat} {d : Backend} (hnd : idsNodup bs)
    (hmove : chosen hash (removeBackend d bs) t k ≠ chosen hash bs t k) :
    ∀ b, chosen hash bs t k = some b → b.id = d.id := by
  intro b hchosen
  by_cases hne : b.id = d.id
  · exact hne
  · exact absurd ((failover_isolation hnd hchosen hne).trans hchosen.symm) hmove

end Sticky
