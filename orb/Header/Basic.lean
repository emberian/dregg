/-
Header — a header list and its rewrite algebra (core).

An HTTP header list is an ordered association list of name/value byte-strings.
Names are compared *case-insensitively* (RFC 7230 §3.2): `Content-Type` and
`content-type` denote the same field.  We model this with a canonicalising map
`canon` (fold ASCII upper-case to lower-case, byte by byte) and compare the
canonical forms.  Because `canon` is a total function and `=` is an equivalence,
the induced name comparison `nameEqb` is an equivalence relation regardless of
what `canon` does internally; that `canon` actually folds case is a separate,
demonstrable fact (see `Header/Hop.lean`).

The rewrite primitives are ordinary pure functions of an explicit list:

  * `get n`      — the first field whose name matches `n` (case-insensitively).
  * `remove n`   — drop *every* field whose name matches `n`.
  * `set n v`    — replace the field(s) named `n` with the single value `v`
                   (modelled as `remove n` then append `⟨n, v⟩`).
  * `add n v`    — append `⟨n, v⟩`, keeping any existing values.

All four are structurally total: no `partial`, no fuel, no failure.  The whole
algebra reduces to two "locality" lemmas, `get_remove` and `get_set`, which say
that a mutation of name `n` changes a lookup of name `m` only when `n` and `m`
name the same field.  Every headline theorem in `Header/Rewrite.lean` follows
from those two.
-/

namespace Header

/-- A header name, as a byte-string. -/
abbrev Name := List UInt8

/-- A header value, as a byte-string. -/
abbrev Value := List UInt8

/-- One header field: a name paired with a value. -/
structure Field where
  name : Name
  value : Value
deriving DecidableEq, Repr

/-- A header list: an ordered association list of fields. -/
abbrev Headers := List Field

def version : String := "0.1.0"

/-! ### Case-insensitive name comparison -/

/-- Fold one ASCII byte to lower case: `A`..`Z` (65..90) map to `a`..`z`. -/
def lowerByte (b : UInt8) : UInt8 :=
  if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then b + 32 else b

/-- Canonical form of a name: lower-case every byte. -/
def canon (n : Name) : Name := n.map lowerByte

/-- Case-insensitive name equality, as a `Bool`. -/
def nameEqb (a b : Name) : Bool := decide (canon a = canon b)

theorem nameEqb_eq {a b : Name} : nameEqb a b = true ↔ canon a = canon b := by
  simp only [nameEqb, decide_eq_true_eq]

theorem nameEqb_false_iff {a b : Name} : nameEqb a b = false ↔ canon a ≠ canon b := by
  simp only [nameEqb, decide_eq_false_iff_not]

/-- `nameEqb` is reflexive. -/
@[simp] theorem nameEqb_refl (a : Name) : nameEqb a a = true := by
  simp only [nameEqb, decide_eq_true_eq]

/-- `nameEqb` is symmetric. -/
theorem nameEqb_symm {a b : Name} (h : nameEqb a b = true) : nameEqb b a = true := by
  rw [nameEqb_eq] at h ⊢; exact h.symm

/-- `nameEqb` is transitive. -/
theorem nameEqb_trans {a b c : Name} (h1 : nameEqb a b = true) (h2 : nameEqb b c = true) :
    nameEqb a c = true := by
  rw [nameEqb_eq] at *; exact h1.trans h2

/-- A field matching a name that is distinct from `m` cannot match `m`:
if `g ~ n` and `n ≁ m` then `g ≁ m`. -/
theorem nameEqb_false_trans {g n m : Name}
    (hgn : nameEqb g n = true) (hnm : nameEqb n m = false) : nameEqb g m = false := by
  rw [nameEqb_false_iff] at hnm ⊢
  rw [nameEqb_eq] at hgn
  intro hgm; exact hnm (hgn.symm.trans hgm)

/-- `nameEqb` is a congruence in its second argument. -/
theorem nameEqb_congr_right {a b : Name} (h : nameEqb a b = true) (c : Name) :
    nameEqb c a = nameEqb c b := by
  have hcanon : canon a = canon b := nameEqb_eq.mp h
  unfold nameEqb; rw [hcanon]

/-- A `nameEqb …  = false` fact discharges the `if`-condition of a name test. -/
theorem name_neq {X Y : Name} (h : nameEqb X Y = false) : ¬ (nameEqb X Y = true) := by
  rw [h]; decide

/-! ### The rewrite primitives -/

/-- The value of the first field whose name matches `n`, if any. -/
def get (n : Name) (h : Headers) : Option Value :=
  (h.find? (fun f => nameEqb f.name n)).map Field.value

/-- Remove every field whose name matches `n`. -/
def remove (n : Name) (h : Headers) : Headers :=
  h.filter (fun f => !nameEqb f.name n)

/-- Set name `n` to value `v`: drop the existing field(s) named `n`, then append
`⟨n, v⟩` so that exactly one field named `n` remains, carrying `v`. -/
def set (n : Name) (v : Value) (h : Headers) : Headers :=
  remove n h ++ [⟨n, v⟩]

/-- Add value `v` under name `n`, appending and keeping any existing values. -/
def add (n : Name) (v : Value) (h : Headers) : Headers :=
  h ++ [⟨n, v⟩]

/-- `n` is one of the names in the hop set `hop` (compared case-insensitively). -/
def isHop (hop : List Name) (n : Name) : Bool := hop.any (fun hn => nameEqb hn n)

/-- Hop-by-hop strip: drop every field whose name is in the hop set `hop`, and
keep every field whose name is not.  A single `filter` — a partition of the
list into stripped and surviving fields. -/
def strip (hop : List Name) (h : Headers) : Headers :=
  h.filter (fun f => !isHop hop f.name)

/-! ### `cons` reductions -/

@[simp] theorem get_nil (n : Name) : get n [] = none := rfl

theorem get_cons (n : Name) (f : Field) (h : Headers) :
    get n (f :: h) = if nameEqb f.name n then some f.value else get n h := by
  simp only [get, List.find?_cons]
  by_cases hb : nameEqb f.name n = true
  · rw [if_pos hb]; simp [hb]
  · rw [if_neg hb]; simp [eq_false_of_ne_true hb]

theorem get_singleton (m : Name) (f : Field) :
    get m [f] = if nameEqb f.name m then some f.value else none := by
  rw [get_cons, get_nil]

theorem remove_cons (n : Name) (f : Field) (t : Headers) :
    remove n (f :: t) = if nameEqb f.name n then remove n t else f :: remove n t := by
  simp only [remove, List.filter_cons]
  by_cases hb : nameEqb f.name n = true
  · rw [if_pos hb]; simp [hb]
  · rw [if_neg hb]; simp [eq_false_of_ne_true hb]

/-! ### `find?`/`get` over append -/

/-- `find?` over an append: the left result wins, else fall through to the right. -/
theorem find?_append {α} (p : α → Bool) (a b : List α) :
    (a ++ b).find? p = (a.find? p).or (b.find? p) := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, List.find?_cons, List.find?_cons]
    cases hp : p x with
    | true => simp
    | false => simp [ih]

/-- If every element fails `p`, `find?` returns `none`. -/
theorem find?_none_of_all {α} (p : α → Bool) (l : List α)
    (H : ∀ x ∈ l, p x = false) : l.find? p = none := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha : p a = false := H a (List.mem_cons_self _ _)
    have ht : ∀ x ∈ t, p x = false := fun x hx => H x (List.mem_cons_of_mem a hx)
    simp [List.find?_cons, ha, ih ht]

theorem get_append (m : Name) (a b : Headers) :
    get m (a ++ b) = (get m a).or (get m b) := by
  unfold get
  rw [find?_append]
  cases a.find? (fun f => nameEqb f.name m) with
  | none => simp
  | some x => simp

/-! ### The two locality lemmas -/

/-- **Locality of `remove`.**  Removing name `n` leaves a lookup of name `m`
unchanged unless `n` and `m` name the same field, in which case the lookup goes
absent. -/
theorem get_remove (n m : Name) (h : Headers) :
    get m (remove n h) = if nameEqb n m then none else get m h := by
  induction h with
  | nil => simp [remove, get]
  | cons f t ih =>
    rw [remove_cons]
    by_cases hfn : nameEqb f.name n = true
    · -- f is removed
      rw [if_pos hfn]
      by_cases hnm : nameEqb n m = true
      · rw [if_pos hnm] at ih ⊢; exact ih
      · rw [if_neg hnm] at ih ⊢
        rw [get_cons]
        have hfmF : nameEqb f.name m = false :=
          nameEqb_false_trans hfn (eq_false_of_ne_true hnm)
        rw [if_neg (name_neq hfmF)]
        exact ih
    · -- f is kept
      rw [if_neg hfn]
      by_cases hnm : nameEqb n m = true
      · rw [if_pos hnm]
        rw [get_cons]
        have hfmF : nameEqb f.name m = false := by
          cases hc : nameEqb f.name m with
          | false => rfl
          | true => exact absurd (nameEqb_trans hc (nameEqb_symm hnm)) hfn
        rw [if_neg (name_neq hfmF)]
        rw [if_pos hnm] at ih
        exact ih
      · rw [if_neg hnm]
        rw [get_cons, get_cons]
        rw [if_neg hnm] at ih
        by_cases hfm : nameEqb f.name m = true
        · rw [if_pos hfm, if_pos hfm]
        · rw [if_neg hfm, if_neg hfm, ih]

/-- **Locality of `set`.**  Setting name `n` to `v` makes a lookup of name `m`
return `v` when `n` and `m` name the same field, and leaves it unchanged
otherwise. -/
theorem get_set (n : Name) (v : Value) (m : Name) (h : Headers) :
    get m (set n v h) = if nameEqb n m then some v else get m h := by
  unfold set
  rw [get_append, get_singleton, get_remove]
  by_cases hnm : nameEqb n m = true
  · simp [hnm]
  · simp [eq_false_of_ne_true hnm]

end Header
