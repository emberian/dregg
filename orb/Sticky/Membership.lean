/-
Sticky.Membership — dynamic upstream-pool membership, and the minimal-disruption
property of consistent hashing stated over the keyed assignment map.

The pool is the eligible list `bs`. Two transitions:

  * **add-backend**: `bs ↦ n :: bs`;
  * **remove-backend**: `bs ↦ removeBackend d bs` (defined in `Sticky.Basic`).

The keyed assignment map is `assign hash bs : Nat → Option Nat`, `k ↦ id of the
rendezvous winner of `bs` for `k`` — the stateless (unpinned) routing map that
the stick table caches on top of. The theorems bound how it changes:

  * `addBackend_keeps_or_moves` — under an add, each key either keeps its old
    winner or moves to the new backend `n`; nothing else can happen.
  * `addBackend_stable` — a key that did not move to `n` keeps its exact old
    backend.
  * `addBackend_assign_off_new` — the assignment map is unchanged on every key
    that is not (re)assigned to `n`'s id: **only keys that hash to the added
    backend move.**
  * `removeBackend_assign_off_dropped` — the assignment map is unchanged on every
    key whose old id was not `d`'s: **only keys that hashed to the removed
    backend move.**

Together these are the minimal-disruption property of consistent hashing over the
keyed assignment map: a one-backend membership change relocates only the keys
belonging to the changed backend. Pins layer on identically — a live pin never
points at the added backend (it is brand new), and `Sticky.Routing`'s
`failover_isolation` handles a removal at the pinned/`chosen` granularity
(`addBackend_pinned_stable` below gives the add direction for pins).
-/

import Sticky.Basic

namespace Sticky

open Proxy

/-- The stateless keyed assignment map: each key to the *id* of its rendezvous
winner over the current pool (or `none` on an empty pool). This is the map a
consistent-hash load balancer materializes; the stick table pins on top of it. -/
def assign (hash : Nat → Nat → Nat) (bs : List Backend) (k : Nat) : Option Nat :=
  (rendezvous hash k bs).map Backend.id

/-! ### Add-backend -/

/-- Adding `n` to the pool moves each key by at most one step: the winner over
`n :: bs` is either the newcomer `n` or the previous winner over `bs`. There is
no third possibility — a key cannot jump to some *other* incumbent. -/
theorem addBackend_keeps_or_moves {hash : Nat → Nat → Nat} {n : Backend}
    {bs : List Backend} {k : Nat} :
    rendezvous hash k (n :: bs) = some n ∨
    rendezvous hash k (n :: bs) = rendezvous hash k bs := by
  cases hr : rendezvous hash k bs with
  | none => left; simp [rendezvous, hr]
  | some c =>
    by_cases hbe : beats hash k n c = true
    · left; simp [rendezvous, hr, hbe]
    · right; simp [rendezvous, hr, hbe]

/-- A key that is not (re)selected onto the newcomer `n` keeps its exact previous
backend. Only keys that now win to `n` move. -/
theorem addBackend_stable {hash : Nat → Nat → Nat} {n : Backend}
    {bs : List Backend} {k : Nat} {c : Backend}
    (hkeep : rendezvous hash k (n :: bs) ≠ some n)
    (hold : rendezvous hash k bs = some c) :
    rendezvous hash k (n :: bs) = some c := by
  rcases addBackend_keeps_or_moves (hash := hash) (n := n) (bs := bs) (k := k) with h | h
  · exact absurd h hkeep
  · rw [h, hold]

/-- **Add is minimal disruption (assignment map).** The keyed assignment map is
unchanged on every key not assigned to the added backend's id: if the new
assignment is not `n.id`, it equals the old assignment. Hence a one-backend
addition relocates only the keys that hash to the newcomer. -/
theorem addBackend_assign_off_new {hash : Nat → Nat → Nat} {n : Backend}
    {bs : List Backend} {k : Nat}
    (hne : assign hash (n :: bs) k ≠ some n.id) :
    assign hash (n :: bs) k = assign hash bs k := by
  simp only [assign] at hne ⊢
  rcases addBackend_keeps_or_moves (hash := hash) (n := n) (bs := bs) (k := k) with h | h
  · rw [h] at hne; simp at hne
  · rw [h]

/-! ### Remove-backend -/

/-- **Remove is minimal disruption (assignment map).** The keyed assignment map
is unchanged on every key whose old assignment was not the removed backend's id.
Hence a one-backend removal relocates only the keys that hashed to the departed
backend; every other key keeps its assignment. -/
theorem removeBackend_assign_off_dropped {hash : Nat → Nat → Nat} {d : Backend}
    {bs : List Backend} {k : Nat} (hnd : idsNodup bs)
    (hne : assign hash bs k ≠ some d.id) :
    assign hash (removeBackend d bs) k = assign hash bs k := by
  simp only [assign] at hne ⊢
  cases hr : rendezvous hash k bs with
  | none =>
    have hbs : bs = [] := rendezvous_eq_none hr
    subst hbs
    rfl
  | some c =>
    have hcd : c.id ≠ d.id := by
      intro heq; apply hne; rw [hr]; simp [heq]
    have hc' : c ∈ removeBackend d bs :=
      mem_removeBackend.mpr ⟨rendezvous_mem hr, hcd⟩
    have hsurv := rendezvous_minimal_disruption hnd (removeBackend_nodup hnd)
      removeBackend_subset hr hc'
    rw [hsurv]

/-! ### Pins under add-backend -/

/-- A live pin is undisturbed by adding a backend: the newcomer cannot displace
an existing eligible pin (nothing is pinned to a brand-new backend, and the old
backend remains eligible). The chosen backend is unchanged. -/
theorem addBackend_pinned_stable {hash : Nat → Nat → Nat} {n : Backend}
    {bs : List Backend} {t : Table} {k bid : Nat} {b : Backend}
    (hnd : idsNodup (n :: bs)) (htk : t k = some bid) (hmem : b ∈ bs)
    (hid : b.id = bid) :
    chosen hash (n :: bs) t k = some b :=
  chosen_of_pin (pinned_of_lookup htk
    (lookupId_eq_some_of_mem hnd (List.mem_cons_of_mem n hmem) hid))

end Sticky
