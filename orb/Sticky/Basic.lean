/-
Sticky — session-affinity routing and dynamic upstream-pool membership.

The load-balancing story (`Proxy.Rendezvous`) supplies a *stateless* affinity
policy: a key routes to the lexicographic-maximum `(hash key id, id)` backend of
the eligible set, with minimal disruption under set change. This module adds the
*stateful* layer on top:

  * a **stickiness table** `Table : Nat → Option Nat` pins a session key to a
    backend *id*. A live pin overrides the stateless choice; a dead pin (its
    backend no longer eligible) is transparently re-computed and re-pinned.
  * **pool membership** transitions — add-backend (`n :: bs`) and remove-backend
    (`removeBackend`) — over the eligible list.

`Basic` fixes the vocabulary: the table, the `lookupId` of a pinned id inside an
eligible list, the pinned/`chosen` resolution, the operational `route` step, and
the `removeBackend` transition, together with the reduction and membership lemmas
the theorem files consume. Everything is a pure function over explicit state;
the healthy/eligible set is passed in, snapshotted, exactly as the selection
call sees it.

`chosen` is the assignment the request observes; `route` additionally returns the
updated table (a fresh pin is written only when the old pin was dead). The two
agree on the backend (`route_snd_eq_chosen`).
-/

import Proxy.Basic
import Proxy.Rendezvous

namespace Sticky

open Proxy

/-- A stickiness table: a session key (`Nat`) is pinned to a backend *id*
(`Nat`), or is unpinned (`none`). Modeled as a total function with an `Option`
codomain — the finite-map view, with `none` = absent. -/
abbrev Table := Nat → Option Nat

/-- Write a pin for `k`, leaving every other key untouched. -/
def update (t : Table) (k : Nat) (v : Nat) : Table :=
  fun k' => if k' = k then some v else t k'

@[simp] theorem update_self (t : Table) (k v : Nat) : update t k v k = some v := by
  simp [update]

theorem update_other (t : Table) (k v k' : Nat) (h : k' ≠ k) :
    update t k v k' = t k' := by simp [update, h]

/-- Find the eligible backend carrying identity `bid`, scanning left to right.
When the eligible list has distinct ids (`idsNodup`) this is the unique such
backend; the scan order is then immaterial. -/
def lookupId (bid : Nat) : List Backend → Option Backend
  | [] => none
  | b :: bs => if b.id = bid then some b else lookupId bid bs

/-- A found backend really carries the queried id. -/
theorem lookupId_id {bid : Nat} {bs : List Backend} {b : Backend}
    (h : lookupId bid bs = some b) : b.id = bid := by
  induction bs with
  | nil => simp [lookupId] at h
  | cons c cs ih =>
    simp only [lookupId] at h
    by_cases hc : c.id = bid
    · rw [if_pos hc] at h; cases h; exact hc
    · rw [if_neg hc] at h; exact ih h

/-- A found backend is a member of the eligible list. -/
theorem lookupId_mem {bid : Nat} {bs : List Backend} {b : Backend}
    (h : lookupId bid bs = some b) : b ∈ bs := by
  induction bs with
  | nil => simp [lookupId] at h
  | cons c cs ih =>
    simp only [lookupId] at h
    by_cases hc : c.id = bid
    · rw [if_pos hc] at h; cases h; exact List.mem_cons_self _ _
    · rw [if_neg hc] at h; exact List.mem_cons_of_mem c (ih h)

/-- Absent id ⇔ failed lookup. The lookup succeeds exactly when the id is
present among the eligible backends. -/
theorem lookupId_eq_none_iff {bid : Nat} {bs : List Backend} :
    lookupId bid bs = none ↔ bid ∉ bs.map Backend.id := by
  induction bs with
  | nil => simp [lookupId]
  | cons c cs ih =>
    simp only [lookupId, List.map_cons, List.mem_cons]
    by_cases hc : c.id = bid
    · simp only [if_pos hc]
      constructor
      · intro h; simp at h
      · intro h; exact absurd (Or.inl hc.symm) h
    · simp only [if_neg hc, ih, not_or]
      exact ⟨fun h => ⟨fun e => hc e.symm, h⟩, fun h => h.2⟩

/-- Under distinct ids, an eligible member is *the* lookup result for its id. -/
theorem lookupId_eq_some_of_mem {bs : List Backend} {b : Backend} {bid : Nat}
    (hnd : idsNodup bs) (hmem : b ∈ bs) (hid : b.id = bid) :
    lookupId bid bs = some b := by
  induction bs with
  | nil => cases hmem
  | cons c cs ih =>
    have hnd' : c.id ∉ cs.map Backend.id ∧ idsNodup cs := by
      simpa [idsNodup] using hnd
    simp only [lookupId]
    rcases List.mem_cons.mp hmem with h | h
    · subst h; simp [hid]
    · by_cases hc : c.id = bid
      · exfalso
        apply hnd'.1
        have hbid : b.id ∈ cs.map Backend.id := List.mem_map_of_mem Backend.id h
        have hcb : c.id = b.id := by rw [hc, hid]
        rw [hcb]; exact hbid
      · simp only [if_neg hc]; exact ih hnd'.2 h

/-- The pinned backend for `k`: the eligible backend named by the pin, when the
pin exists *and* names an eligible id; otherwise `none` (unpinned, or the pin is
dead — its backend has left the eligible set). -/
def pinned (bs : List Backend) (t : Table) (k : Nat) : Option Backend :=
  match t k with
  | none => none
  | some bid => lookupId bid bs

theorem pinned_none_of_unpinned {bs : List Backend} {t : Table} {k : Nat}
    (h : t k = none) : pinned bs t k = none := by simp only [pinned, h]

theorem pinned_of_lookup {bs : List Backend} {t : Table} {k bid : Nat}
    {b : Backend} (htk : t k = some bid) (hl : lookupId bid bs = some b) :
    pinned bs t k = some b := by simp only [pinned, htk, hl]

theorem pinned_none_of_dead {bs : List Backend} {t : Table} {k bid : Nat}
    (htk : t k = some bid) (hl : lookupId bid bs = none) :
    pinned bs t k = none := by simp only [pinned, htk, hl]

/-- The backend a request observes for key `k`: honour a live pin, otherwise the
stateless rendezvous winner of the current eligible set. -/
def chosen (hash : Nat → Nat → Nat) (bs : List Backend) (t : Table) (k : Nat) :
    Option Backend :=
  match pinned bs t k with
  | some b => some b
  | none => rendezvous hash k bs

theorem chosen_of_pin {hash : Nat → Nat → Nat} {bs : List Backend} {t : Table}
    {k : Nat} {b : Backend} (h : pinned bs t k = some b) :
    chosen hash bs t k = some b := by simp only [chosen, h]

theorem chosen_of_no_pin {hash : Nat → Nat → Nat} {bs : List Backend} {t : Table}
    {k : Nat} (h : pinned bs t k = none) :
    chosen hash bs t k = rendezvous hash k bs := by simp only [chosen, h]

/-- The chosen backend is always an eligible member (a live pin or the winner). -/
theorem chosen_mem {hash : Nat → Nat → Nat} {bs : List Backend} {t : Table}
    {k : Nat} {b : Backend} (h : chosen hash bs t k = some b) : b ∈ bs := by
  cases htk : t k with
  | none =>
    rw [chosen_of_no_pin (pinned_none_of_unpinned htk)] at h
    exact rendezvous_mem h
  | some bid =>
    cases hl : lookupId bid bs with
    | some pb =>
      rw [chosen_of_pin (pinned_of_lookup htk hl)] at h
      have : pb = b := Option.some.inj h
      subst this; exact lookupId_mem hl
    | none =>
      rw [chosen_of_no_pin (pinned_none_of_dead htk hl)] at h
      exact rendezvous_mem h

/-- One routing step. Returns the updated table and the chosen backend. A live
pin is honoured with the table untouched; a dead-or-absent pin falls to the
rendezvous winner, which is then written back as the new pin. On an empty
eligible set nothing is chosen and nothing is pinned. -/
def route (hash : Nat → Nat → Nat) (bs : List Backend) (t : Table) (k : Nat) :
    Table × Option Backend :=
  match pinned bs t k with
  | some b => (t, some b)
  | none =>
    match rendezvous hash k bs with
    | some b => (update t k b.id, some b)
    | none => (t, none)

/-- The backend `route` returns is exactly `chosen` — the table bookkeeping does
not affect which backend is selected. -/
theorem route_snd_eq_chosen (hash : Nat → Nat → Nat) (bs : List Backend)
    (t : Table) (k : Nat) : (route hash bs t k).2 = chosen hash bs t k := by
  simp only [route, chosen]
  cases pinned bs t k with
  | some b => rfl
  | none => cases rendezvous hash k bs <;> rfl

/-! ### The remove-backend pool transition -/

/-- Remove every backend carrying `d`'s identity from the eligible list. With
distinct ids this drops exactly `d`. Membership shrink is modeled as a filter so
the subset and nodup facts are immediate. -/
def removeBackend (d : Backend) (bs : List Backend) : List Backend :=
  bs.filter (fun b => decide (b.id ≠ d.id))

theorem mem_removeBackend {d b : Backend} {bs : List Backend} :
    b ∈ removeBackend d bs ↔ b ∈ bs ∧ b.id ≠ d.id := by
  simp only [removeBackend, List.mem_filter, decide_eq_true_eq]

theorem removeBackend_subset {d : Backend} {bs : List Backend} :
    ∀ c ∈ removeBackend d bs, c ∈ bs :=
  fun _ hc => (mem_removeBackend.mp hc).1

theorem removeBackend_nodup {d : Backend} {bs : List Backend}
    (hnd : idsNodup bs) : idsNodup (removeBackend d bs) := by
  have hsub : List.Sublist ((removeBackend d bs).map Backend.id) (bs.map Backend.id) :=
    (List.filter_sublist bs).map Backend.id
  exact hsub.nodup hnd

end Sticky
