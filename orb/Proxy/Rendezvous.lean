/-
Rendezvous — highest-random-weight (rendezvous) hashing, the affinity policy.

Each (key, backend) pair gets a score `hash key backend.id`; the key is routed
to the backend with the highest score, ties broken by the higher backend id.
The hash function is an arbitrary parameter — every theorem below holds for
EVERY `hash : Nat → Nat → Nat`, so nothing here depends on distribution
quality (that is a statistical property, measured, not proved).

Why rendezvous rather than a ketama-style ring: the two are interchangeable
as *policies* (pure function key → backend, minimal disruption on membership
change), and rendezvous admits a two-line spec — the winner is the unique
lexicographic maximum of `(score, id)` — from which the disruption theorem
falls out. A ring is an optimization of the same spec for large backend sets;
if the engine ships a ring, it must refine `rendezvous` pointwise (that is a
differential-test obligation, not a new proof).

The theorems:

  * `rendezvous_total` / `rendezvous_mem` — the totality/soundness pair;
  * `rendezvous_spec` — the winner characterization (beats every other id);
  * `rendezvous_minimal_disruption` — **the** consistent-hashing property:
    shrink the candidate set any way you like; every key whose backend
    survived still maps to the same backend. Only keys whose backend left
    move.
  * `rendezvous_ignores_load` — affinity is a function of ids alone: load
    counters, weights, health flapping of OTHER fields do not move keys
    (membership changes do, per the disruption theorem).
-/

import Proxy.Basic

namespace Proxy

/-- Strict lexicographic "b beats c" on `(hash key ·.id, ·.id)`. For distinct
ids this is a strict total order, so the maximum is unique. -/
def beats (hash : Nat → Nat → Nat) (key : Nat) (b c : Backend) : Bool :=
  decide (hash key c.id < hash key b.id) ||
    (decide (hash key b.id = hash key c.id) && decide (c.id < b.id))

theorem beats_trans {hash : Nat → Nat → Nat} {key : Nat} {a b c : Backend}
    (hab : beats hash key a b = true) (hbc : beats hash key b c = true) :
    beats hash key a c = true := by
  simp only [beats, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem beats_total {hash : Nat → Nat → Nat} {key : Nat} {b c : Backend}
    (hne : b.id ≠ c.id) :
    beats hash key b c = true ∨ beats hash key c b = true := by
  simp only [beats, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem beats_asymm {hash : Nat → Nat → Nat} {key : Nat} {b c : Backend}
    (h : beats hash key b c = true) : beats hash key c b = false := by
  simp only [beats, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [beats, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  omega

/-- Rendezvous selection: the lexicographic-maximum backend for this key. -/
def rendezvous (hash : Nat → Nat → Nat) (key : Nat) : List Backend → Option Backend
  | [] => none
  | b :: bs =>
    match rendezvous hash key bs with
    | none => some b
    | some c => if beats hash key b c then some b else some c

/-! ### Totality and membership -/

theorem rendezvous_total {hash : Nat → Nat → Nat} {key : Nat}
    {bs : List Backend} (h : bs ≠ []) : (rendezvous hash key bs).isSome := by
  cases bs with
  | nil => exact absurd rfl h
  | cons b rest =>
    cases hr : rendezvous hash key rest with
    | none => simp [rendezvous, hr]
    | some c =>
      by_cases hb : beats hash key b c = true <;> simp [rendezvous, hr, hb]

theorem rendezvous_mem {hash : Nat → Nat → Nat} {key : Nat}
    {bs : List Backend} {b : Backend} (h : rendezvous hash key bs = some b) :
    b ∈ bs := by
  induction bs generalizing b with
  | nil => cases h
  | cons c rest ih =>
    cases hr : rendezvous hash key rest with
    | none =>
      simp only [rendezvous, hr] at h
      cases h
      exact List.mem_cons_self c rest
    | some w =>
      simp only [rendezvous, hr] at h
      split at h
      · cases h; exact List.mem_cons_self c rest
      · cases h; exact List.mem_cons_of_mem _ (ih hr)

theorem rendezvous_eq_none {hash : Nat → Nat → Nat} {key : Nat}
    {bs : List Backend} (h : rendezvous hash key bs = none) : bs = [] := by
  cases bs with
  | nil => rfl
  | cons b rest =>
    have := rendezvous_total (hash := hash) (key := key)
      (bs := b :: rest) (by intro hc; cases hc)
    rw [h] at this
    cases this

/-! ### The winner characterization -/

/-- The winner beats every other identity in the candidate list. -/
theorem rendezvous_beats_all {hash : Nat → Nat → Nat} {key : Nat}
    {bs : List Backend} {b : Backend} (hnd : idsNodup bs)
    (hsel : rendezvous hash key bs = some b) :
    ∀ c ∈ bs, c.id ≠ b.id → beats hash key b c = true := by
  induction bs generalizing b with
  | nil => cases hsel
  | cons a rest ih =>
    have hnd' : a.id ∉ rest.map Backend.id ∧ idsNodup rest := by
      simpa [idsNodup] using hnd
    intro c hc hcid
    cases hr : rendezvous hash key rest with
    | none =>
      have hrest : rest = [] := rendezvous_eq_none hr
      simp only [rendezvous, hr] at hsel
      cases hsel
      rcases List.mem_cons.mp hc with hc' | hc'
      · exact absurd (by rw [hc']) hcid
      · rw [hrest] at hc'; cases hc'
    | some w =>
      simp only [rendezvous, hr] at hsel
      have hw_mem : w ∈ rest := rendezvous_mem hr
      by_cases hbeats : beats hash key a w = true
      · -- winner is the head `a`
        rw [if_pos hbeats] at hsel
        cases hsel
        rcases List.mem_cons.mp hc with hc' | hc'
        · exact absurd (by rw [hc']) hcid
        · by_cases hcw : c.id = w.id
          · have hcweq : c = w := eq_of_id_eq hnd'.2 hc' hw_mem hcw
            rw [hcweq]; exact hbeats
          · exact beats_trans hbeats (ih hnd'.2 hr c hc' hcw)
      · -- winner is the tail winner `w`
        rw [if_neg hbeats] at hsel
        cases hsel
        rcases List.mem_cons.mp hc with hc' | hc'
        · subst hc'
          rcases beats_total (hash := hash) (key := key) hcid with h | h
          · exact absurd h hbeats
          · exact h
        · exact ih hnd'.2 hr c hc' hcid

/-- Conversely: a member that beats every other identity is the winner. -/
theorem rendezvous_of_beats_all {hash : Nat → Nat → Nat} {key : Nat}
    {bs : List Backend} {b : Backend} (hnd : idsNodup bs) (hb : b ∈ bs)
    (hall : ∀ c ∈ bs, c.id ≠ b.id → beats hash key b c = true) :
    rendezvous hash key bs = some b := by
  induction bs with
  | nil => cases hb
  | cons a rest ih =>
    have hnd' : a.id ∉ rest.map Backend.id ∧ idsNodup rest := by
      simpa [idsNodup] using hnd
    rcases List.mem_cons.mp hb with hb' | hb'
    · -- b is the head
      rw [hb'] at hall ⊢
      cases hr : rendezvous hash key rest with
      | none => simp [rendezvous, hr]
      | some w =>
        have hw_mem : w ∈ rest := rendezvous_mem hr
        have hwid : w.id ≠ a.id := by
          intro heq
          apply hnd'.1
          rw [← heq]
          exact List.mem_map_of_mem Backend.id hw_mem
        simp [rendezvous, hr,
          hall w (List.mem_cons_of_mem _ hw_mem) hwid]
    · -- b is in the tail
      have hbid : b.id ≠ a.id := by
        intro heq
        apply hnd'.1
        rw [← heq]
        exact List.mem_map_of_mem Backend.id hb'
      have htail : rendezvous hash key rest = some b :=
        ih hnd'.2 hb' (fun c hc hcid =>
          hall c (List.mem_cons_of_mem _ hc) hcid)
      have hba : beats hash key b a = true :=
        hall a (List.mem_cons_self a rest) (fun h => hbid h.symm)
      simp [rendezvous, htail, beats_asymm hba]

/-! ### Minimal disruption -/

/-- **Minimal disruption.** Shrink the candidate set arbitrarily (backends
leave — health, drain, scale-down). Every key whose winning backend is still
present keeps exactly that backend. Contrapositive: a key moves only when its
backend left the eligible set. This holds for every hash function and every
subset — not just single-backend removals. -/
theorem rendezvous_minimal_disruption {hash : Nat → Nat → Nat} {key : Nat}
    {bs bs' : List Backend} {b : Backend}
    (hnd : idsNodup bs) (hnd' : idsNodup bs')
    (hsub : ∀ c ∈ bs', c ∈ bs)
    (hsel : rendezvous hash key bs = some b) (hb' : b ∈ bs') :
    rendezvous hash key bs' = some b :=
  rendezvous_of_beats_all hnd' hb'
    (fun c hc hcid => rendezvous_beats_all hnd hsel c (hsub c hc) hcid)

/-! ### Load-independence (affinity) -/

/-- Selection is a function of the identity list alone: two candidate lists
with the same ids in the same order (weights, connection counts, tiers all
free to differ) produce winners with the same id. Key affinity therefore
survives load changes and weight reconfiguration; only membership changes can
move a key. -/
theorem rendezvous_ignores_load {hash : Nat → Nat → Nat} {key : Nat}
    {bs bs' : List Backend}
    (hids : bs.map Backend.id = bs'.map Backend.id) :
    (rendezvous hash key bs).map Backend.id
      = (rendezvous hash key bs').map Backend.id := by
  induction bs generalizing bs' with
  | nil =>
    cases bs' with
    | nil => rfl
    | cons b' rest' => simp at hids
  | cons a rest ih =>
    cases bs' with
    | nil => simp at hids
    | cons a' rest' =>
      simp only [List.map_cons, List.cons.injEq] at hids
      have hrec := ih hids.2
      cases hr : rendezvous hash key rest with
      | none =>
        cases hr' : rendezvous hash key rest' with
        | none => simp [rendezvous, hr, hr', hids.1]
        | some w' => rw [hr, hr'] at hrec; simp at hrec
      | some w =>
        cases hr' : rendezvous hash key rest' with
        | none => rw [hr, hr'] at hrec; simp at hrec
        | some w' =>
          rw [hr, hr'] at hrec
          have hwid : w.id = w'.id := by simpa using hrec
          have hbeats : beats hash key a w = beats hash key a' w' := by
            simp only [beats, hids.1, hwid]
          by_cases hb : beats hash key a w = true
          · have hb' : beats hash key a' w' = true := hbeats ▸ hb
            simp [rendezvous, hr, hr', hb, hb', hids.1]
          · have hb' : ¬ beats hash key a' w' = true := fun h =>
              hb (hbeats.symm ▸ h)
            simp [rendezvous, hr, hr', hb, hb', hwid]

end Proxy
