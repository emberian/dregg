/-
Route.Path — path normalization over segment lists.

A request-target path is modelled as a `List String`: the segments between
slashes, already split. Working over segments (not the raw string) is a
deliberate design decision — it makes the RFC 3986 §5.2.4 `remove_dot_segments`
walk a plain list fold and keeps every theorem an induction on the segment list.

The normalization pipeline has two stages with a strict order:

  1. `decodeSegs` — percent-decode each segment EXACTLY ONCE (the boundary
     transform). Decoding is deliberately NOT part of the repeatedly-applied
     core: percent-decoding is not idempotent (`%252e` → `%2e` → `.`), so a
     second decode is a traversal vulnerability, not a no-op. The pipeline
     therefore decodes at the boundary and never again.

  2. `removeDotSegments` — the RFC 3986 dot-segment walk, over ALREADY-decoded
     segments, in the ABSOLUTE (rooted / clamped) variant a server applies to a
     request path: `.` is dropped, `..` pops the previous output segment or is
     dropped at the root (you cannot climb above `/`). This is the idempotent
     core and the one that carries the safety content.

Theorems:
  * `removeDotSegments_idem`     — normalization is idempotent.
  * `removeDotSegments_noDot`    — a normalized path contains no dot-segments.
  * `resolveUnder_root_prefix`   — resolving a normalized relative path under a
                                   configured root keeps the root as a prefix
                                   (path-traversal safety as a prefix invariant),
    strengthened by `descend_resolveUnder_root_prefix`: the root stays a prefix
    even under a filesystem interpreter that actually pops on `..`, because the
    resolved tail carries no `..` to pop with.
-/

namespace Route.Path

/-! ## Percent-decode boundary (run exactly once) -/

/-- Hex-digit value, or `none` for a non-hex character. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Percent-decode a character stream once: `%HH` with two hex digits becomes
the decoded byte; a malformed escape is left verbatim (the three characters
pass through unchanged). Structurally recursive on the character list, so it
reduces definitionally. -/
def decodeChars : List Char → List Char
  | [] => []
  | '%' :: h :: l :: rest =>
    match hexVal h, hexVal l with
    | some hi, some lo => Char.ofNat (hi * 16 + lo) :: decodeChars rest
    | _, _ => '%' :: h :: l :: decodeChars rest
  | c :: rest => c :: decodeChars rest

/-- Percent-decode a single segment, once. -/
def decodeSeg (s : String) : String := ⟨decodeChars s.toList⟩

/-- Percent-decode every segment of a path, once. -/
def decodeSegs (segs : List String) : List String := segs.map decodeSeg

/-! ### Decode is a once-only boundary (why it is not in the idempotent core)

These concrete witnesses show percent-decode is NOT idempotent, so it must run
exactly once. `%252e` decoded once is the harmless literal `%2e`; decoded a
second time it collapses to `.`, a dot-segment that would then evade the walk.
The pipeline below decodes once and reruns only `removeDotSegments`. -/

theorem decode_encoded_dotdot :
    decodeChars ['%','2','e','%','2','e'] = ['.', '.'] := by decide

theorem decode_not_idempotent_once :
    decodeChars ['%','2','5','2','e'] = ['%','2','e'] := by decide

theorem decode_not_idempotent_twice :
    decodeChars (decodeChars ['%','2','5','2','e']) = ['.'] := by decide

/-! ## RFC 3986 remove_dot_segments (absolute / clamped variant) -/

/-- A dot-segment is `"."` (current dir) or `".."` (parent dir). -/
def IsDot (s : String) : Prop := s = "." ∨ s = ".."

instance : DecidablePred IsDot := fun s => by
  unfold IsDot; exact inferInstance

/-- The output stack walk. `acc` holds the output segments in REVERSE order.
`.` is dropped; `..` pops one output segment or is dropped at the root (clamp);
anything else is pushed. -/
def rds : List String → List String → List String
  | acc, [] => acc.reverse
  | acc, s :: rest =>
    if s = "." then rds acc rest
    else if s = ".." then
      (match acc with
       | [] => rds [] rest
       | _ :: acc' => rds acc' rest)
    else rds (s :: acc) rest

/-- RFC 3986 §5.2.4 dot-segment removal over a decoded segment list. -/
def removeDotSegments (segs : List String) : List String := rds [] segs

/-- Full normalization: decode once, then remove dot-segments. -/
def normalize (segs : List String) : List String :=
  removeDotSegments (decodeSegs segs)

/-! ### No dot-segments in the output -/

/-- Every segment produced by `rds` is a non-dot segment, provided the seed
accumulator already holds only non-dot segments. -/
theorem rds_noDot {acc segs : List String}
    (hacc : ∀ s ∈ acc, ¬ IsDot s) :
    ∀ s ∈ rds acc segs, ¬ IsDot s := by
  induction segs generalizing acc with
  | nil =>
    intro s hs
    simp only [rds, List.mem_reverse] at hs
    exact hacc s hs
  | cons a rest ih =>
    intro s hs
    unfold rds at hs
    by_cases h1 : a = "."
    · rw [if_pos h1] at hs; exact ih hacc s hs
    · rw [if_neg h1] at hs
      by_cases h2 : a = ".."
      · rw [if_pos h2] at hs
        cases acc with
        | nil => exact ih (by intro x hx; cases hx) s hs
        | cons b acc' =>
          apply ih _ s hs
          intro x hx
          exact hacc x (List.mem_cons_of_mem _ hx)
      · rw [if_neg h2] at hs
        apply ih _ s hs
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · subst hx; intro hdot; rcases hdot with hd | hd
          · exact h1 hd
          · exact h2 hd
        · exact hacc x hx

/-- **A normalized path contains no dot-segments.** -/
theorem removeDotSegments_noDot (segs : List String) :
    ∀ s ∈ removeDotSegments segs, ¬ IsDot s :=
  rds_noDot (by intro s hs; cases hs)

/-- Corollary on the full pipeline. -/
theorem normalize_noDot (segs : List String) :
    ∀ s ∈ normalize segs, ¬ IsDot s :=
  removeDotSegments_noDot _

/-! ### Idempotence -/

/-- On a dot-free input, `rds` performs only pushes: the result is the reversed
seed followed by the input verbatim. -/
theorem rds_id_of_noDot {acc segs : List String}
    (h : ∀ s ∈ segs, ¬ IsDot s) :
    rds acc segs = acc.reverse ++ segs := by
  induction segs generalizing acc with
  | nil => simp [rds]
  | cons a rest ih =>
    have ha : ¬ IsDot a := h a (List.mem_cons_self a rest)
    have h1 : a ≠ "." := fun hd => ha (Or.inl hd)
    have h2 : a ≠ ".." := fun hd => ha (Or.inr hd)
    have hrest : ∀ s ∈ rest, ¬ IsDot s := fun s hs => h s (List.mem_cons_of_mem _ hs)
    unfold rds
    rw [if_neg h1, if_neg h2, ih hrest]
    simp

/-- On a dot-free input, `removeDotSegments` is the identity. -/
theorem removeDotSegments_id_of_noDot {segs : List String}
    (h : ∀ s ∈ segs, ¬ IsDot s) :
    removeDotSegments segs = segs := by
  unfold removeDotSegments
  rw [rds_id_of_noDot h]
  simp

/-- **Normalization is idempotent** (on the dot-segment core). -/
theorem removeDotSegments_idem (segs : List String) :
    removeDotSegments (removeDotSegments segs) = removeDotSegments segs :=
  removeDotSegments_id_of_noDot (removeDotSegments_noDot segs)

/-- **The full pipeline is a fixed point of the pure core.** Re-normalizing an
already-normalized path reruns only `removeDotSegments` — it does NOT decode a
second time. This is the "decode once, no double-decode" discipline made
formal: the safe operation to re-run is `removeDotSegments`, never `decodeSegs`,
and rerunning it changes nothing. -/
theorem normalize_fixed (segs : List String) :
    removeDotSegments (normalize segs) = normalize segs :=
  removeDotSegments_idem (decodeSegs segs)

/-! ## Path-traversal safety as a prefix invariant

`resolveUnder root rel` joins a configured root prefix onto the normalized
relative path. Because the normalized tail carries no `..` segments, the root
is preserved as a prefix under any filesystem interpretation. -/

/-- Resolve a relative segment list under a configured root: normalize the
relative path, then join it onto the root. -/
def resolveUnder (root rel : List String) : List String :=
  root ++ removeDotSegments rel

/-- **Structural prefix invariant.** The configured root is always a prefix of
the resolved path. -/
theorem resolveUnder_root_prefix (root rel : List String) :
    root <+: resolveUnder root rel :=
  List.prefix_append root (removeDotSegments rel)

/-- The resolved tail contains no `..` — so no filesystem `..` pop can escape
the root. This is what makes the prefix invariant non-vacuous under real
directory semantics. -/
theorem resolveUnder_tail_no_parent (rel : List String) :
    ∀ s ∈ removeDotSegments rel, s ≠ ".." := by
  intro s hs hbad
  exact removeDotSegments_noDot rel s hs (Or.inr hbad)

/-! ### The prefix invariant survives a `..`-popping interpreter

`descend base segs` is the naive joiner a traversal attack targets: it walks
`segs` and on `..` actually pops a segment off the accumulated path. The safety
theorem: because the resolved tail has no `..`, `descend` never pops, so the
root remains a prefix even under this interpretation. -/

/-- Filesystem-style descent that pops on `..` (unclamped). -/
def descend : List String → List String → List String
  | base, [] => base
  | base, s :: rest =>
    if s = ".." then descend base.dropLast rest
    else if s = "." then descend base rest
    else descend (base ++ [s]) rest

/-- On a list with no `..` and no `.`, `descend` never pops: it just appends. -/
theorem descend_noDot {base segs : List String}
    (h : ∀ s ∈ segs, ¬ IsDot s) :
    descend base segs = base ++ segs := by
  induction segs generalizing base with
  | nil => simp [descend]
  | cons a rest ih =>
    have ha : ¬ IsDot a := h a (List.mem_cons_self a rest)
    have h1 : a ≠ ".." := fun hd => ha (Or.inr hd)
    have h2 : a ≠ "." := fun hd => ha (Or.inl hd)
    have hrest : ∀ s ∈ rest, ¬ IsDot s := fun s hs => h s (List.mem_cons_of_mem _ hs)
    unfold descend
    rw [if_neg h1, if_neg h2, ih hrest]
    simp

/-- **Traversal safety under a popping interpreter.** Given a clean configured
root (a real directory path carries no dot-segments), walking the resolved path
from the empty base with the `..`-popping `descend` reproduces the resolved path
exactly (no pop fires), so the root stays a prefix. An attacker's encoded `..`
cannot climb out of the root: it was removed before resolution. -/
theorem descend_resolveUnder_root_prefix (root rel : List String)
    (hroot : ∀ s ∈ root, ¬ IsDot s) :
    root <+: descend [] (resolveUnder root rel) := by
  have hno : ∀ s ∈ resolveUnder root rel, ¬ IsDot s := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hroot s hs
    · exact removeDotSegments_noDot rel s hs
  rw [descend_noDot hno, List.nil_append]
  exact resolveUnder_root_prefix root rel

end Route.Path
