/-
Route.Match — host/route matching as a total function with a precedence order.

A route table is a `List (Route H)`. Each route carries a path pattern that is
exactly one of three precedence classes:

  * `exact`   — the request segment list equals the pattern (rank 2, highest);
  * `prefix`  — the pattern is a prefix of the request (rank 1);
  * `default` — matches unconditionally (rank 0, the explicit catch-all).

Matching selects with two rules, in order:

  1. **class precedence** — exact beats prefix beats default;
  2. **least index** — among routes of the winning class, the earliest in the
     table wins (the first-match tie-break, no ambiguity).

`bestMatch` realizes this as `find?`-first per class, tried highest-class-first,
so both rules hold by construction.

Theorems:
  * `bestMatch_total`     — a table containing a default always matches (totality:
                            always some route, never a stuck request).
  * `bestMatch_sound`     — the chosen route actually matches the request.
  * `bestMatch_mem`       — the chosen route is in the table.
  * `bestMatch_class_max` — determinism: no matching route outranks the chosen
                            one (the chosen route is a highest-precedence match).
  * `bestMatch_is_first_of_class` — determinism: the chosen route is the FIRST
                            route of the winning class (least-index tie-break).
-/

namespace Route.Match

/-- A compiled path pattern over segment lists, one per precedence class. -/
inductive Pat where
  | exact (segs : List String)
  | «prefix» (segs : List String)
  | «default»
deriving Repr

/-- A route: a pattern plus a handler of arbitrary type `H`. -/
structure Route (H : Type) where
  pat : Pat
  handler : H

variable {H : Type}

/-- Precedence rank of a class: exact (2) > prefix (1) > default (0). -/
def classRank : Pat → Nat
  | .exact _ => 2
  | .prefix _ => 1
  | .default => 0

/-! ### Per-class match predicates (Bool, one true per route at most) -/

/-- The route is an exact route whose pattern equals the request. -/
def matchesExact (req : List String) : Route H → Bool :=
  fun r => match r.pat with | .exact s => decide (req = s) | _ => false

/-- The route is a prefix route whose pattern is a prefix of the request. -/
def matchesPrefix (req : List String) : Route H → Bool :=
  fun r => match r.pat with | .prefix s => s.isPrefixOf req | _ => false

/-- The route is the default route. -/
def matchesDefault : Route H → Bool :=
  fun r => match r.pat with | .default => true | _ => false

/-- The route matches the request in some class. -/
def matchesAny (req : List String) (r : Route H) : Bool :=
  matchesExact req r || matchesPrefix req r || matchesDefault r

/-- **Route selection.** Try the highest class first; within a class take the
first (least-index) match. -/
def bestMatch (rt : List (Route H)) (req : List String) : Option (Route H) :=
  match rt.find? (matchesExact req) with
  | some r => some r
  | none =>
    match rt.find? (matchesPrefix req) with
    | some r => some r
    | none => rt.find? matchesDefault

/-! ### Small list helpers (kept local to avoid core-API name drift) -/

theorem find?_isSome_of_mem {α} {p : α → Bool} {a : α} {l : List α}
    (hmem : a ∈ l) (hp : p a = true) : (l.find? p).isSome := by
  induction l with
  | nil => cases hmem
  | cons b rest ih =>
    rcases List.mem_cons.mp hmem with h | h
    · subst h; simp [List.find?, hp]
    · cases hb : p b with
      | true => simp [List.find?, hb]
      | false => simp only [List.find?, hb]; exact ih h

theorem find?_all_false_of_none {α} {p : α → Bool} {l : List α}
    (h : l.find? p = none) : ∀ a ∈ l, p a = false := by
  induction l with
  | nil => intro a ha; cases ha
  | cons b rest ih =>
    intro a ha
    cases hb : p b with
    | true => rw [List.find?, hb] at h; cases h
    | false =>
      rw [List.find?, hb] at h
      rcases List.mem_cons.mp ha with h' | h'
      · subst h'; exact hb
      · exact ih h a h'

theorem find?_pred_true {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : p a = true := by
  induction l with
  | nil => simp [List.find?] at h
  | cons b rest ih =>
    cases hb : p b with
    | true => rw [List.find?, hb] at h; cases h; exact hb
    | false => rw [List.find?, hb] at h; exact ih h

theorem find?_mem {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : a ∈ l := by
  induction l with
  | nil => simp [List.find?] at h
  | cons b rest ih =>
    cases hb : p b with
    | true => rw [List.find?, hb] at h; cases h; exact List.mem_cons_self _ _
    | false => rw [List.find?, hb] at h; exact List.mem_cons_of_mem _ (ih h)

/-! ### Pattern classification -/

theorem matchesExact_exact {req : List String} {r : Route H}
    (h : matchesExact req r = true) : ∃ s, r.pat = Pat.exact s := by
  unfold matchesExact at h
  cases hp : r.pat with
  | exact s => exact ⟨s, rfl⟩
  | «prefix» s => rw [hp] at h; simp at h
  | «default» => rw [hp] at h; simp at h

theorem matchesPrefix_prefix {req : List String} {r : Route H}
    (h : matchesPrefix req r = true) : ∃ s, r.pat = Pat.prefix s := by
  unfold matchesPrefix at h
  cases hp : r.pat with
  | exact s => rw [hp] at h; simp at h
  | «prefix» s => exact ⟨s, rfl⟩
  | «default» => rw [hp] at h; simp at h

theorem matchesDefault_default {r : Route H}
    (h : matchesDefault r = true) : r.pat = Pat.default := by
  unfold matchesDefault at h
  cases hp : r.pat with
  | exact s => rw [hp] at h; simp at h
  | «prefix» s => rw [hp] at h; simp at h
  | «default» => rfl

/-- If a route matches in any class, its own class is the one that fired: the
Bool `matchesAny` collapses to the single predicate its constructor allows. -/
theorem matchesAny_exact {req : List String} {r : Route H} {s : List String}
    (hp : r.pat = Pat.exact s) : matchesAny req r = matchesExact req r := by
  unfold matchesAny matchesPrefix matchesDefault
  rw [hp]; simp

theorem matchesAny_prefix {req : List String} {r : Route H} {s : List String}
    (hp : r.pat = Pat.prefix s) : matchesAny req r = matchesPrefix req r := by
  unfold matchesAny matchesExact matchesDefault
  rw [hp]; simp

theorem matchesAny_default {req : List String} {r : Route H}
    (hp : r.pat = Pat.default) : matchesAny req r = matchesDefault r := by
  unfold matchesAny matchesExact matchesPrefix
  rw [hp]; simp

/-! ### Totality -/

/-- **Match totality.** A route table that contains a default route always
returns some route (the request is never stuck). -/
theorem bestMatch_total {rt : List (Route H)} {req : List String}
    (hdef : ∃ r ∈ rt, matchesDefault r = true) :
    (bestMatch rt req).isSome := by
  obtain ⟨rd, hmem, hd⟩ := hdef
  unfold bestMatch
  cases he : rt.find? (matchesExact req) with
  | some r => simp
  | none =>
    cases hpf : rt.find? (matchesPrefix req) with
    | some r => simp
    | none => simpa using find?_isSome_of_mem hmem hd

/-! ### Soundness + membership -/

/-- **Soundness.** The chosen route matches the request. -/
theorem bestMatch_sound {rt : List (Route H)} {req : List String} {r : Route H}
    (h : bestMatch rt req = some r) : matchesAny req r = true := by
  unfold bestMatch at h
  cases he : rt.find? (matchesExact req) with
  | some re =>
    rw [he] at h; cases h
    have hx := find?_pred_true he
    obtain ⟨s, hp⟩ := matchesExact_exact hx
    rw [matchesAny_exact hp]; exact hx
  | none =>
    rw [he] at h
    cases hpf : rt.find? (matchesPrefix req) with
    | some rp =>
      rw [hpf] at h; cases h
      have hx := find?_pred_true hpf
      obtain ⟨s, hp⟩ := matchesPrefix_prefix hx
      rw [matchesAny_prefix hp]; exact hx
    | none =>
      rw [hpf] at h
      have hx := find?_pred_true h
      have hp := matchesDefault_default hx
      rw [matchesAny_default hp]; exact hx

/-- **Membership.** The chosen route is drawn from the table. -/
theorem bestMatch_mem {rt : List (Route H)} {req : List String} {r : Route H}
    (h : bestMatch rt req = some r) : r ∈ rt := by
  unfold bestMatch at h
  cases he : rt.find? (matchesExact req) with
  | some re => rw [he] at h; cases h; exact find?_mem he
  | none =>
    rw [he] at h
    cases hpf : rt.find? (matchesPrefix req) with
    | some rp => rw [hpf] at h; cases h; exact find?_mem hpf
    | none => rw [hpf] at h; exact find?_mem h

/-! ### Determinism -/

/-- **Determinism (class precedence).** No route matching the request has a
strictly higher precedence class than the chosen one — the chosen route is a
highest-precedence match. -/
theorem bestMatch_class_max {rt : List (Route H)} {req : List String} {r : Route H}
    (h : bestMatch rt req = some r) :
    ∀ r' ∈ rt, matchesAny req r' = true → classRank r'.pat ≤ classRank r.pat := by
  unfold bestMatch at h
  cases he : rt.find? (matchesExact req) with
  | some re =>
    -- winner is exact (rank 2 = maximum)
    rw [he] at h; cases h
    obtain ⟨s, hp⟩ := matchesExact_exact (find?_pred_true he)
    intro r' _ _
    rw [hp]; cases r'.pat <;> simp [classRank]
  | none =>
    rw [he] at h
    have hnoExact := find?_all_false_of_none he
    cases hpf : rt.find? (matchesPrefix req) with
    | some rp =>
      -- winner is prefix (rank 1); no exact match exists, so rank ≤ 1
      rw [hpf] at h; cases h
      obtain ⟨s, hp⟩ := matchesPrefix_prefix (find?_pred_true hpf)
      intro r' hmem hany
      rw [hp]
      -- goal: classRank r'.pat ≤ 1
      cases hp' : r'.pat with
      | exact s' =>
        exfalso
        have : matchesExact req r' = true := by
          have := matchesAny_exact (req := req) (r := r') hp'
          rw [this] at hany; exact hany
        rw [hnoExact r' hmem] at this; cases this
      | «prefix» s' => simp [classRank]
      | «default» => simp [classRank]
    | none =>
      -- winner is default (rank 0); neither exact nor prefix matches exist
      rw [hpf] at h
      have hnoPrefix := find?_all_false_of_none hpf
      obtain hp := matchesDefault_default (find?_pred_true h)
      intro r' hmem hany
      rw [hp]
      cases hp' : r'.pat with
      | exact s' =>
        exfalso
        have : matchesExact req r' = true := by
          have := matchesAny_exact (req := req) (r := r') hp'
          rw [this] at hany; exact hany
        rw [hnoExact r' hmem] at this; cases this
      | «prefix» s' =>
        exfalso
        have : matchesPrefix req r' = true := by
          have := matchesAny_prefix (req := req) (r := r') hp'
          rw [this] at hany; exact hany
        rw [hnoPrefix r' hmem] at this; cases this
      | «default» => simp [classRank]

/-- **Determinism (least-index within class).** The chosen route is the first
route of the winning class in table order: every earlier route fails the
winning class's predicate. Phrased on the winning-class `find?`, which is what
`bestMatch` returns. -/
theorem bestMatch_is_first_of_class {rt : List (Route H)} {req : List String}
    {r : Route H} (h : bestMatch rt req = some r) :
    (rt.find? (matchesExact req) = some r)
      ∨ (rt.find? (matchesExact req) = none ∧ rt.find? (matchesPrefix req) = some r)
      ∨ (rt.find? (matchesExact req) = none ∧ rt.find? (matchesPrefix req) = none
          ∧ rt.find? matchesDefault = some r) := by
  unfold bestMatch at h
  cases he : rt.find? (matchesExact req) with
  | some re => rw [he] at h; cases h; exact Or.inl rfl
  | none =>
    rw [he] at h
    cases hpf : rt.find? (matchesPrefix req) with
    | some rp => rw [hpf] at h; cases h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | none => rw [hpf] at h; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩)

end Route.Match
