/-
# Last-Event-ID resumption

A reconnecting client presents the id of the last event it saw. The server
resumes by replaying the events **strictly after** that id — no event already
seen is re-sent (no replay), and no event after it is skipped (no skip).

History is the broadcaster's published stream: a `List (Nat × Event)` tagged
with sequence ids, which `Sse.Broadcast` guarantees is strictly increasing
(`published_pairwise`). `resumeAfter L h` is the suffix of `h` past the first
entry whose id is `L`.

Theorems:

* `resumeAfter_sublist` — the replay is an order-preserving subsequence of the
  history (only real events, never reordered, never duplicated).
* `resumeAfter_exact` / `resumeAfter_reconstruct` — with the id present exactly
  once (guaranteed by the strictly-increasing ids), the replay is precisely the
  tail after that id: `seenPrefix ++ (L, e) :: replay = history`. **No replay,
  no skip.**
* `resumeAfter_gt` — with strictly-increasing ids, every replayed event has id
  strictly greater than `L`: resumption starts at exactly the event after `L`.
* `resumeAfter_absent` — an unknown id replays nothing (resume live).
-/
import Sse.Basic
import Sse.Broadcast

namespace Sse

/-- The replay for a client whose last-seen id is `L`: the events strictly after
the first history entry tagged `L`. -/
def resumeAfter (L : Nat) : List (Nat × Event) → List (Nat × Event)
  | [] => []
  | (i, _) :: rest => if i = L then rest else resumeAfter L rest

/-- **Replay soundness.** The replay is a subsequence of the history: it never
invents, reorders, or duplicates an event. -/
theorem resumeAfter_sublist (L : Nat) (h : List (Nat × Event)) :
    (resumeAfter L h).Sublist h := by
  induction h with
  | nil => exact List.Sublist.refl _
  | cons p rest ih =>
    obtain ⟨i, e⟩ := p
    simp only [resumeAfter]
    by_cases hi : i = L
    · rw [if_pos hi]; exact (List.Sublist.refl rest).cons (i, e)
    · rw [if_neg hi]; exact ih.cons (i, e)

/-- **Exact resumption (no replay, no skip).** If the last-seen id `L` occurs at
a point with no earlier occurrence — `history = before ++ (L, e) :: after` and
`L` is not among the ids of `before` — then the replay is exactly `after`: every
already-seen event (`before` and the `L` event itself) is excluded, and every
later event is included. -/
theorem resumeAfter_exact (L : Nat) (before after : List (Nat × Event)) (e : Event)
    (hbefore : L ∉ before.map Prod.fst) :
    resumeAfter L (before ++ (L, e) :: after) = after := by
  induction before with
  | nil => simp [resumeAfter]
  | cons p bs ih =>
    obtain ⟨i, ev⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at hbefore
    obtain ⟨hi, hrest⟩ := hbefore
    have hiL : i ≠ L := fun h => hi h.symm
    simp only [List.cons_append, resumeAfter]
    rw [if_neg hiL]
    exact ih hrest

/-- **Reconstruction: no gap, no duplicate at the seam.** The already-seen
prefix (through the `L` event) followed by the replay reconstructs the full
history exactly — the client's cursor advances by precisely the events it had
not seen. -/
theorem resumeAfter_reconstruct (L : Nat) (before after : List (Nat × Event))
    (e : Event) (hbefore : L ∉ before.map Prod.fst) :
    before ++ (L, e) :: resumeAfter L (before ++ (L, e) :: after)
      = before ++ (L, e) :: after := by
  rw [resumeAfter_exact L before after e hbefore]

/-- **Resume from exactly the event after `L`.** When the history's ids are
strictly increasing (as the broadcaster guarantees, `published_pairwise`), every
replayed event has an id strictly greater than `L`: nothing at or before the
last-seen id is re-sent. -/
theorem resumeAfter_gt (L : Nat) (h : List (Nat × Event))
    (hs : h.Pairwise (fun a b => a.1 < b.1)) :
    ∀ p ∈ resumeAfter L h, L < p.1 := by
  induction h with
  | nil => intro p hp; simp [resumeAfter] at hp
  | cons q rest ih =>
    obtain ⟨i, e⟩ := q
    rw [List.pairwise_cons] at hs
    obtain ⟨hhead, htail⟩ := hs
    simp only [resumeAfter]
    by_cases hi : i = L
    · rw [if_pos hi]
      intro p hp
      have := hhead p hp
      simp only at this
      rw [hi] at this; exact this
    · rw [if_neg hi]
      exact ih htail

/-- An unknown last-seen id replays nothing: the client resumes from the live
edge. -/
theorem resumeAfter_absent (L : Nat) (h : List (Nat × Event))
    (habsent : L ∉ h.map Prod.fst) :
    resumeAfter L h = [] := by
  induction h with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨i, e⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at habsent
    obtain ⟨hi, hrest⟩ := habsent
    have hiL : i ≠ L := fun h => hi h.symm
    simp only [resumeAfter]
    rw [if_neg hiL]
    exact ih hrest

/-! ## Coupling to the broadcaster stream -/

/-- Over a real published stream the ids are strictly increasing, so a present
last-seen id triggers a replay of exactly the strictly-later events. This
instantiates `resumeAfter_gt` at `published ops`. -/
theorem resumeAfter_published_gt (L : Nat) (ops : List Op) :
    ∀ p ∈ resumeAfter L (published ops), L < p.1 :=
  resumeAfter_gt L (published ops) (published_pairwise ops)

/-! ## Wire vectors, checker-verified -/

/-- Resume after id `1` on a three-event history replays exactly ids `2, 3`. -/
example :
    resumeAfter 1 [(0, Event.empty), (1, Event.empty), (2, Event.empty), (3, Event.empty)]
      = [(2, Event.empty), (3, Event.empty)] := rfl

/-- Resume after an unknown id replays nothing. -/
example :
    resumeAfter 9 [(0, Event.empty), (1, Event.empty)] = [] := rfl

end Sse
