/-
RouteCorrect — route selection *correctness*: a refinement of `bestMatch`
against an independent precedence specification.

`Route.Match` proves SAFETY-flavoured facts about `bestMatch`: the chosen route
matches (`bestMatch_sound`), is in the table (`bestMatch_mem`), no matching
route outranks it (`bestMatch_class_max`), and it is the first of its class
(`bestMatch_is_first_of_class`). Those pin down properties of the *output*, but
they do not, on their own, say the function computes THE route an RFC-style
precedence rule dictates: a degenerate selector could satisfy several of them in
isolation.

This file closes that gap with a single equation. It defines, *without any
reference to* `bestMatch`, what the selected route SHOULD be:

  * `specMatches` — the RFC matching relation per class (exact ⇒ segment lists
    equal; prefix ⇒ pattern is a prefix of the request; default ⇒ always);
  * `specRank`    — the precedence rank of a class (exact 2 ≻ prefix 1 ≻ default
    0), i.e. "most specific first";
  * `specBest`    — the argmax over the table under that precedence: among all
    matching routes take the one of greatest rank, breaking ties by declaration
    order (earliest wins). This is written as an order-directed fold, NOT by
    calling `bestMatch`.

The correctness theorem is `bestMatch_refines_spec : bestMatch rt req =
specBest rt req` for every table and request. It is non-vacuous: a selector that
returned the FIRST matching route regardless of class (the naive router bug)
disagrees with `specBest` on a table where a prefix route is declared before an
exact route that also matches — see `naive_first_differs` / `specBest_picks_exact`
below, where the two selectors return handlers `0` and `1` respectively.

RFC basis. RFC 9110 §4 fixes the target as an origin-form path; matching a
request against a configured set of routes is a server responsibility (RFC 9110
§3.3, §7.4). The precedence used here — an exact path beats a prefix (path-prefix)
route, which beats the catch-all, with declaration order as the deterministic
tie-break — is the standard "most-specific-match-wins" discipline. Prefix routes
form a single rank; among equally-ranked matches the earliest declaration is
authoritative (a deterministic, order-independent-of-input rule).
-/

import Route.Match

namespace RouteCorrect

open Route.Match

variable {H : Type}

/-! ## Independent specification of the RFC precedence rule -/

/-- **Matching relation (per class), specified directly from the RFC shapes.**
An exact route matches a request iff their segment lists are equal; a prefix
route matches iff its pattern is a prefix of the request segments; the default
route matches unconditionally. Defined by case on the pattern — it does not call
any part of `bestMatch`. -/
def specMatches (req : List String) (r : Route H) : Bool :=
  match r.pat with
  | .exact s => decide (req = s)
  | .prefix s => s.isPrefixOf req
  | .default => true

/-- **Precedence rank ("most specific first").** Exact (2) outranks prefix (1)
outranks default (0). -/
def specRank : Pat → Nat
  | .exact _ => 2
  | .prefix _ => 1
  | .default => 0

/-- **The specified best route: the precedence argmax.** Fold the table keeping,
among matching routes, the one of greatest `specRank`; on a rank tie keep the
route already held (the earlier declaration). This is the maximum matching route
under (rank desc, declaration-order asc) — defined by the ORDER, independently of
`bestMatch`. -/
def specBest : List (Route H) → List String → Option (Route H)
  | [], _ => none
  | r :: rs, req =>
    if specMatches req r then
      match specBest rs req with
      | none => some r
      | some b => if specRank b.pat ≤ specRank r.pat then some r else some b
    else specBest rs req

/-! ## Refinement proof -/

@[simp] theorem specRank_exact (s : List String) : specRank (Pat.exact s) = 2 := rfl
@[simp] theorem specRank_prefix (s : List String) : specRank (Pat.prefix s) = 1 := rfl
@[simp] theorem specRank_default : specRank Pat.default = 0 := rfl

theorem specRank_le_two (p : Pat) : specRank p ≤ 2 := by
  cases p <;> simp [specRank]

theorem exact_specRank {req : List String} {r : Route H}
    (h : matchesExact req r = true) : specRank r.pat = 2 := by
  obtain ⟨s, hp⟩ := matchesExact_exact h; simp [specRank, hp]

theorem prefix_specRank {req : List String} {r : Route H}
    (h : matchesPrefix req r = true) : specRank r.pat = 1 := by
  obtain ⟨s, hp⟩ := matchesPrefix_prefix h; simp [specRank, hp]

theorem default_specRank {r : Route H}
    (h : matchesDefault r = true) : specRank r.pat = 0 := by
  simp [specRank, matchesDefault_default h]

/-- `find?` on a cons, as an `if`. -/
theorem find?_cons {α} (p : α → Bool) (a : α) (l : List α) :
    (a :: l).find? p = if p a then some a else l.find? p := by
  cases h : p a <;> simp [List.find?, h]

/-- `bestMatch` unfolded to its staged three-`find?` form (definitional). -/
theorem bestMatch_def (rt : List (Route H)) (req : List String) :
    bestMatch rt req =
      match rt.find? (matchesExact req) with
      | some r => some r
      | none =>
        match rt.find? (matchesPrefix req) with
        | some r => some r
        | none => rt.find? matchesDefault := rfl

/-- When no exact route matches, `bestMatch` returns a route of rank ≤ 1. -/
theorem bestMatch_noExact_rank {rs : List (Route H)} {req : List String} {b : Route H}
    (he : rs.find? (matchesExact req) = none) (hb : bestMatch rs req = some b) :
    specRank b.pat ≤ 1 := by
  rw [bestMatch_def, he] at hb
  simp only at hb
  cases hp : rs.find? (matchesPrefix req) with
  | some p =>
    rw [hp] at hb
    simp only [Option.some.injEq] at hb
    subst hb
    have := prefix_specRank (find?_pred_true hp); omega
  | none =>
    rw [hp] at hb
    simp only at hb
    have := default_specRank (find?_pred_true hb); omega

/-- **Argmax recursion for `bestMatch`.** The staged three-`find?` selector
satisfies the same one-step precedence-argmax recursion that DEFINES `specBest`.
This is the whole content of the refinement: the implementation, which never
compares ranks explicitly, nevertheless keeps the head exactly when the head is
the (weakly) higher-ranked match. -/
theorem bestMatch_step (r : Route H) (rs : List (Route H)) (req : List String) :
    bestMatch (r :: rs) req =
      (if specMatches req r then
        match bestMatch rs req with
        | none => some r
        | some b => if specRank b.pat ≤ specRank r.pat then some r else some b
       else bestMatch rs req) := by
  cases hpat : r.pat with
  | exact s =>
    have hE : matchesExact req r = decide (req = s) := by simp [matchesExact, hpat]
    have hP : matchesPrefix req r = false := by simp [matchesPrefix, hpat]
    have hD : matchesDefault r = false := by simp [matchesDefault, hpat]
    have hSM : specMatches req r = decide (req = s) := by simp [specMatches, hpat]
    have hSR : specRank r.pat = 2 := by simp [specRank, hpat]
    rw [bestMatch_def (r :: rs), find?_cons (matchesExact req) r rs,
        find?_cons (matchesPrefix req) r rs, find?_cons matchesDefault r rs, hE, hP, hD]
    simp only [hSM, if_false]
    by_cases hm : req = s
    · subst hm
      cases hb : bestMatch rs req with
      | none => simp [hb]
      | some b => simp [hb, specRank_le_two b.pat]
    · rw [bestMatch_def rs]
      simp [hm]
  | «prefix» s =>
    have hE : matchesExact req r = false := by simp [matchesExact, hpat]
    have hP : matchesPrefix req r = s.isPrefixOf req := by simp [matchesPrefix, hpat]
    have hD : matchesDefault r = false := by simp [matchesDefault, hpat]
    have hSM : specMatches req r = s.isPrefixOf req := by simp [specMatches, hpat]
    have hSR : specRank r.pat = 1 := by simp [specRank, hpat]
    rw [bestMatch_def (r :: rs), find?_cons (matchesExact req) r rs,
        find?_cons (matchesPrefix req) r rs, find?_cons matchesDefault r rs, hE, hP, hD]
    simp only [hSM, if_false]
    cases hpre : s.isPrefixOf req with
    | false =>
      rw [bestMatch_def rs]; simp [hpre]
    | true =>
      cases he : rs.find? (matchesExact req) with
      | some e =>
        have hb : bestMatch rs req = some e := by simp [bestMatch_def, he]
        have hrank : specRank e.pat = 2 := exact_specRank (find?_pred_true he)
        simp [hpre, he, hb, hrank]
      | none =>
        cases hb : bestMatch rs req with
        | none => simp [hpre, he, hb]
        | some b =>
          have hbnd : specRank b.pat ≤ 1 := bestMatch_noExact_rank he hb
          simp [hpre, he, hb, hbnd]
  | «default» =>
    have hE : matchesExact req r = false := by simp [matchesExact, hpat]
    have hP : matchesPrefix req r = false := by simp [matchesPrefix, hpat]
    have hD : matchesDefault r = true := by simp [matchesDefault, hpat]
    have hSM : specMatches req r = true := by simp [specMatches, hpat]
    have hSR : specRank r.pat = 0 := by simp [specRank, hpat]
    rw [bestMatch_def (r :: rs), find?_cons (matchesExact req) r rs,
        find?_cons (matchesPrefix req) r rs, find?_cons matchesDefault r rs, hE, hP, hD]
    simp only [hSM, if_false, if_true]
    cases he : rs.find? (matchesExact req) with
    | some e =>
      have hb : bestMatch rs req = some e := by simp [bestMatch_def, he]
      have hrank : specRank e.pat = 2 := exact_specRank (find?_pred_true he)
      simp [he, hb, hrank]
    | none =>
      cases hp : rs.find? (matchesPrefix req) with
      | some p =>
        have hb : bestMatch rs req = some p := by simp [bestMatch_def, he, hp]
        have hrank : specRank p.pat = 1 := prefix_specRank (find?_pred_true hp)
        simp [he, hp, hb, hrank]
      | none =>
        cases hd : rs.find? matchesDefault with
        | some d =>
          have hb : bestMatch rs req = some d := by simp [bestMatch_def, he, hp, hd]
          have hrank : specRank d.pat = 0 := default_specRank (find?_pred_true hd)
          simp [he, hp, hd, hb, hrank]
        | none =>
          have hb : bestMatch rs req = none := by simp [bestMatch_def, he, hp, hd]
          simp [he, hp, hd, hb]

/-- **`specBest` equals `bestMatch`.** Both satisfy the same base case and the
same one-step argmax recursion (`bestMatch_step`), so they agree on every table. -/
theorem specBest_eq_bestMatch (rt : List (Route H)) (req : List String) :
    specBest rt req = bestMatch rt req := by
  induction rt with
  | nil => simp [specBest, bestMatch, List.find?]
  | cons r rs ih =>
    rw [bestMatch_step, ← ih]
    simp only [specBest]

/-- **Route-selection refinement.** The implementation `bestMatch` returns
exactly the precedence-argmax route mandated by the specification, for every
route table and request. -/
theorem bestMatch_refines_spec (rt : List (Route H)) (req : List String) :
    bestMatch rt req = specBest rt req :=
  (specBest_eq_bestMatch rt req).symm

/-! ## Non-vacuity: a naive first-match selector fails the spec

The table `egTable` declares a prefix route (handler `0`) BEFORE an exact route
(handler `1`); the request `["a"]` matches both. A selector that returned the
first matching route of any class returns handler `0`; the precedence spec — and
`bestMatch` — return the exact route, handler `1`. The two selectors disagree, so
`bestMatch_refines_spec` genuinely forces the precedence choice: it would be
FALSE for the naive selector. -/

/-- The exact route (segment list `["a"]`), handler `1`. -/
def exR : Route Nat := { pat := .exact ["a"], handler := 1 }

/-- The prefix route (pattern `["a"]`), handler `0`, declared FIRST. -/
def prR : Route Nat := { pat := .prefix ["a"], handler := 0 }

/-- Prefix route declared before the exact route; both match `["a"]`. -/
def egTable : List (Route Nat) := [prR, exR]

def egReq : List String := ["a"]

/-- Both routes match the request. -/
theorem both_match : specMatches egReq prR = true ∧ specMatches egReq exR = true := by
  decide

/-- The naive "first match of any class" selector returns the prefix handler `0`. -/
theorem naive_first_handler :
    (egTable.find? (matchesAny egReq)).map (·.handler) = some 0 := by decide

/-- The precedence spec returns the exact handler `1`. -/
theorem specBest_picks_exact :
    (specBest egTable egReq).map (·.handler) = some 1 := by decide

/-- `bestMatch` agrees with the spec (handler `1`), not the naive selector. -/
theorem best_picks_exact :
    (bestMatch egTable egReq).map (·.handler) = some 1 := by decide

/-- **The two selectors genuinely disagree here.** The naive first-match choice
is not what `bestMatch` computes — so the refinement theorem is not vacuous. -/
theorem naive_first_differs :
    (egTable.find? (matchesAny egReq)).map (·.handler)
      ≠ (bestMatch egTable egReq).map (·.handler) := by decide

end RouteCorrect
