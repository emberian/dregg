/-
# Dregg2.Crypto.HandlebarsGuardedParse — the VERIFIER-SIDE half: a language member IS a render.

Everything the guarded-templater stack proved so far runs GENERATOR → OUTPUT:
`HandlebarsGuarded.guarded_render_mem_language` consumes a `d` already in hand
(`guardedSafe T d → render T d ∈ (guardedToGrammar T).language`), and
`HandlebarsGuardedUniqueness.guarded_render_injective` says AT MOST ONE guard-satisfied `d` can
produce a given output. Neither one lets a party holding only `(T, output)` conclude anything: the
existence / PARSE direction

    output ∈ (guardedToGrammar T).language → ∃ d, guardedSafe T d ∧ render T d = output

was an OPEN residual, named three times in the tree (`Handlebars.lean` §9 `RESIDUAL (round_trip)`,
`HandlebarsUniqueness.lean` §6 `RESIDUAL (general_round_trip)`, `HandlebarsGuarded.lean` §7
`RESIDUAL (guarded_uniqueness)`). This module DISCHARGES it, and composes it with the existing
injectivity into a real `∃!`.

## The class where it is TRUE (named in the theorem, not buried)

The parse direction needs **DISTINCT HOLE IDS** (`(holesOf T).Nodup`) — and nothing else. It does NOT
need separation: separation is what makes the recovered data UNIQUE, not what makes it EXIST.

Distinctness is genuinely load-bearing, not hygiene: a template naming the SAME hole twice renders it
twice with the SAME data, while the language lets the two spans differ, so language members exist that
no assignment renders. `nodup_is_load_bearing` (§6) PROVES this — a `SeparatedTemplate` whose two holes
share id `0`, and a language member of even length while every render of it has odd length. That is the
exact dual of `HandlebarsGuardedUniqueness.abutting_ambiguous` (which proves the separation
side-condition load-bearing for UNIQUENESS): one wall per direction, both demonstrated.

## What is proven (no `sorry`, no new axioms)

* `assign` — the EXTRACTOR: read the per-hole data straight off a span decomposition. Computable, so
  the recovered `d` can be run (§5 `#guard`s evaluate it on a concrete output).
* `parse_exists_distinct_holes` — THE THEOREM: for `(holesOf T).Nodup`, every member of the induced
  language is `render T d` for some guard-satisfying `d`. Proof rides `GuardedSpans`'
  `mem_language_iff_spans` (membership ⇔ a per-segment span decomposition, literals pinned and hole
  spans matcher-attested) and reads `d` off the spans.
* `separated_parse_unique_pointwise` / `separated_parse_exists_unique` — the `∃!` the stack has been
  claiming and not owning: on a `SeparatedTemplate` with distinct hole ids, a language member
  determines its per-hole data EXACTLY ONE way. The second form is a literal `ExistsUnique`, over the
  ordered hole-data vector `(holesOf T).map d` — the honest object, since `d`'s values OFF `holesOf T`
  are unconstrained by the output (a raw `∃! d` is FALSE for that reason alone).
* `Demo` (§5) — the theorem FIRES: a separated 2-hole template and the concrete output
  `data { { {` are fed in and the recovered `d` is COMPUTED — hole 0 ↦ `[data]`, hole 1 ↦ `[{, {]` —
  with the guards re-run on the recovered data by the verified matcher. `#guard`s pin every value.

Axiom hygiene: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. New file; imports
read-only (this module edits nothing).
-/
import Dregg2.Crypto.GuardedSpans
import Dregg2.Crypto.HandlebarsGuardedUniqueness
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsGuardedParse

open Dregg2.Exec
open Dregg2.Crypto
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Crypto.HandlebarsGuarded
open Dregg2.Crypto.GuardedSpans (SpanOk mem_language_iff_spans)
open Dregg2.Crypto.HandlebarsGuardedUniqueness
  (holeIds holesOf SeparatedTemplate guarded_render_injective SepSpine spineSegs spineTemplate
   Separated noBraceRE noBraceRE_excludes derives_noBraceRE_of_nofire render_spine_cons
   render_spine_last)

/-! ## §1 Bookkeeping — hole-ids and render-congruence. -/

/-- A hole named by a segment list is named by its `holeIds`. -/
theorem mem_holeIds : ∀ {segs : List GSeg} {id : Nat} {g : PredRE},
    GSeg.hole id g ∈ segs → id ∈ holeIds segs
  | [], _, _, h => absurd h (by simp)
  | GSeg.lit _ :: rest, id, g, h => by
      have h' : GSeg.hole id g ∈ rest := by
        rcases List.mem_cons.mp h with heq | hin
        · exact absurd heq (by simp)
        · exact hin
      simpa only [holeIds] using mem_holeIds h'
  | GSeg.hole id0 g0 :: rest, id, g, h => by
      rcases List.mem_cons.mp h with heq | hin
      · simp only [GSeg.hole.injEq] at heq
        simp only [holeIds, List.mem_cons]
        exact Or.inl heq.1
      · simp only [holeIds, List.mem_cons]
        exact Or.inr (mem_holeIds hin)

/-- Rendering only reads `d` at the segment list's own hole-ids, so assignments agreeing there
render identically. -/
theorem render_congr (d d' : Nat → List Value) : ∀ segs : List GSeg,
    (∀ id ∈ holeIds segs, d id = d' id) →
    segs.flatMap (renderSeg d) = segs.flatMap (renderSeg d')
  | [], _ => rfl
  | GSeg.lit text :: rest, h => by
      simp only [List.flatMap_cons, renderSeg]
      rw [render_congr d d' rest (by intro id hid; exact h id (by simpa only [holeIds] using hid))]
  | GSeg.hole id0 g0 :: rest, h => by
      simp only [List.flatMap_cons, renderSeg]
      rw [h id0 (by simp [holeIds])]
      rw [render_congr d d' rest
        (by intro id hid
            exact h id (by simp only [holeIds, List.mem_cons]; exact Or.inr hid))]

/-! ## §2 `assign` — THE EXTRACTOR: read the per-hole data off a span decomposition.

`GuardedSpans.mem_language_iff_spans` turns membership into a per-segment span list. `assign` walks
segments and spans in lockstep and hands each hole-id the span sitting at its position. It is a plain
computable function, so the recovered assignment can be RUN (§5). -/

/-- **`assign segs spans`** — the hole-assignment read off a span decomposition: the hole at position
`i` is given `spans[i]`; ids not named by `segs` get `[]`. -/
def assign : List GSeg → List (List Value) → Nat → List Value
  | GSeg.hole id _ :: segs, s :: spans => fun i => if i = id then s else assign segs spans i
  | GSeg.lit _ :: segs, _ :: spans => assign segs spans
  | [], _ => fun _ => []
  | _ :: _, [] => fun _ => []

/-- **`assign_guardedSafe`** — every hole's RECOVERED data satisfies that hole's OWN guard, decided by
the verified matcher. The obligation is exactly the `SpanOk` hole clause; distinctness of hole ids is
what guarantees the span `assign` hands back at `id` is the span `SpanOk` constrained. -/
theorem assign_guardedSafe : ∀ (segs : List GSeg) (spans : List (List Value)),
    SpanOk segs spans → (holeIds segs).Nodup →
    ∀ id g, GSeg.hole id g ∈ segs → derives (assign segs spans id) g = true
  | [], _, _, _, _, _, hmem => absurd hmem (by simp)
  | GSeg.lit _ :: rest, [], hok, _, _, _, _ => absurd hok (by simp [SpanOk])
  | GSeg.hole _ _ :: rest, [], hok, _, _, _, _ => absurd hok (by simp [SpanOk])
  | GSeg.lit text :: rest, s :: spans, hok, hnd, id, g, hmem => by
      obtain ⟨-, hrest⟩ := hok
      have hmem' : GSeg.hole id g ∈ rest := by
        rcases List.mem_cons.mp hmem with heq | hin
        · exact absurd heq (by simp)
        · exact hin
      simpa only [assign] using
        assign_guardedSafe rest spans hrest (by simpa only [holeIds] using hnd) id g hmem'
  | GSeg.hole id0 g0 :: rest, s :: spans, hok, hnd, id, g, hmem => by
      obtain ⟨hguard, hrest⟩ := hok
      rw [holeIds, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with heq | hin
      · simp only [GSeg.hole.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simpa only [assign, if_pos rfl, if_true] using hguard
      · have hne : id ≠ id0 := fun hEq => hnd.1 (hEq ▸ mem_holeIds hin)
        simp only [assign, if_neg hne]
        exact assign_guardedSafe rest spans hrest hnd.2 id g hin

/-- **`assign_render`** — the RECOVERED assignment reproduces the word: rendering the segments under
`assign` reconstructs exactly the concatenation of the spans. Distinctness of hole ids is load-bearing
here too: `assign` gives a repeated id its FIRST span, so the id's later occurrence would print that
first span again instead of its own (§6 turns this into a proved counterexample). -/
theorem assign_render : ∀ (segs : List GSeg) (spans : List (List Value)),
    SpanOk segs spans → (holeIds segs).Nodup →
    segs.flatMap (renderSeg (assign segs spans)) = spans.flatten
  | [], [], _, _ => rfl
  | [], _ :: _, hok, _ => absurd hok (by simp [SpanOk])
  | GSeg.lit _ :: rest, [], hok, _ => absurd hok (by simp [SpanOk])
  | GSeg.hole _ _ :: rest, [], hok, _ => absurd hok (by simp [SpanOk])
  | GSeg.lit text :: rest, s :: spans, hok, hnd => by
      obtain ⟨rfl, hrest⟩ := hok
      simp only [assign, List.flatMap_cons, renderSeg, List.flatten_cons]
      rw [assign_render rest spans hrest (by simpa only [holeIds] using hnd)]
  | GSeg.hole id0 g0 :: rest, s :: spans, hok, hnd => by
      obtain ⟨-, hrest⟩ := hok
      rw [holeIds, List.nodup_cons] at hnd
      have hoff : ∀ id ∈ holeIds rest,
          assign (GSeg.hole id0 g0 :: rest) (s :: spans) id = assign rest spans id := by
        intro id hid
        have hne : id ≠ id0 := fun hEq => hnd.1 (hEq ▸ hid)
        simp only [assign, if_neg hne]
      simp only [List.flatMap_cons, renderSeg, List.flatten_cons]
      rw [show assign (GSeg.hole id0 g0 :: rest) (s :: spans) id0 = s by
            simp [assign]]
      rw [render_congr _ (assign rest spans) rest hoff]
      rw [assign_render rest spans hrest hnd.2]

/-! ## §3 THE THEOREM — the verifier-side existence / parse direction. -/

/-- **`parse_exists_distinct_holes`** — THE VERIFIER-SIDE HALF, on the DISTINCT-HOLE-ID class. A party
holding only `(T, output)` and a proof that `output` is in `T`'s induced language may conclude that
`output` IS an expansion of `T`: there EXISTS per-hole data, each piece satisfying its OWN guard
(decided by the verified matcher), whose render is exactly `output`. Nothing not generated by `T`
under its guards can sit in the language.

The side-condition is `(holesOf T).Nodup` — the template names each hole at most once — and it is
genuinely required (`nodup_is_load_bearing`, §6), NOT an artifact of the proof. Separation is NOT
required here: separation buys UNIQUENESS of the recovered data (§4), not its existence.

Route: `GuardedSpans.mem_language_iff_spans` converts membership into a per-segment span
decomposition (literal spans pinned to the template text, hole spans matcher-attested); `assign`
reads the data off those spans; §2 discharges both obligations. -/
theorem parse_exists_distinct_holes (T : GuardedTemplate) (hnd : (holesOf T).Nodup)
    (output : List Value) (hmem : output ∈ (guardedToGrammar T).language) :
    ∃ d : Nat → List Value, guardedSafe T d ∧ render T d = output := by
  obtain ⟨spans, hok, rfl⟩ := (mem_language_iff_spans T output).mp hmem
  exact ⟨assign T.segments spans,
         assign_guardedSafe T.segments spans hok hnd,
         assign_render T.segments spans hok hnd⟩

/-! ## §4 The `∃!` — composing the new existence half with the landed injectivity. -/

/-- **`separated_parse_unique_pointwise`** — EXISTENCE + UNIQUENESS, pointwise form. On a
`SeparatedTemplate` with distinct hole ids, every language member is the render of guard-satisfying
data, and that data is forced on every hole the template names. Existence is
`parse_exists_distinct_holes` (§3); uniqueness is
`HandlebarsGuardedUniqueness.guarded_render_injective`. This is the round trip, both halves owned. -/
theorem separated_parse_unique_pointwise (T : GuardedTemplate)
    (hsep : SeparatedTemplate T) (hnd : (holesOf T).Nodup)
    (output : List Value) (hmem : output ∈ (guardedToGrammar T).language) :
    ∃ d : Nat → List Value,
      guardedSafe T d ∧ render T d = output ∧
      ∀ d' : Nat → List Value, guardedSafe T d' → render T d' = output →
        ∀ h ∈ holesOf T, d' h = d h := by
  obtain ⟨d, hsafe, hrender⟩ := parse_exists_distinct_holes T hnd output hmem
  refine ⟨d, hsafe, hrender, fun d' hsafe' hr' => ?_⟩
  exact guarded_render_injective T hsep d' d hsafe' hsafe (by rw [hr', hrender])

/-- **`separated_parse_exists_unique`** — a literal `ExistsUnique`, over the object that IS determined:
the ordered per-hole data vector `(holesOf T).map d`. On a `SeparatedTemplate` with distinct hole ids,
a language member has EXACTLY ONE guard-satisfying hole-data vector.

Stated on the vector rather than on `d` itself deliberately: `d`'s values at ids the template does NOT
name are unconstrained by the output, so a raw `∃! d` would be FALSE for a trivial reason. The vector
is the honest carrier of "the data that produced this output". -/
theorem separated_parse_exists_unique (T : GuardedTemplate)
    (hsep : SeparatedTemplate T) (hnd : (holesOf T).Nodup)
    (output : List Value) (hmem : output ∈ (guardedToGrammar T).language) :
    ∃! ds : List (List Value),
      ∃ d : Nat → List Value, guardedSafe T d ∧ render T d = output ∧ (holesOf T).map d = ds := by
  obtain ⟨d, hsafe, hrender, huniq⟩ :=
    separated_parse_unique_pointwise T hsep hnd output hmem
  refine ⟨(holesOf T).map d, ⟨d, hsafe, hrender, rfl⟩, ?_⟩
  rintro ds ⟨d', hsafe', hr', rfl⟩
  exact List.map_congr_left (huniq d' hsafe' hr')

/-! ## §5 NON-VACUITY — the theorem FIRES, and the recovered data COMPUTES.

The template is `HandlebarsGuardedUniqueness.Demo.demoSpine`:
`hole 0 (noBraceRE) · lit[{] · hole 1 (star any)` — separated (hole 0's guard excludes the `{`
delimiter), distinct ids `[0, 1]`. The output fed in is `data { { {` — written as a LITERAL WORD, never
as `render T d` for some hand-chosen `d`. It reaches the parse theorem only as a language member, and
the assignment comes back out. Hole 1's recovered data is a DOUBLE brace — admitted by its permissive
guard, REJECTED by hole 0's — so the recovery is discriminating, not a constant. -/

namespace Demo

open Dregg2.Crypto.HandlebarsGuardedUniqueness.Demo (demoSpine demoSpine_separated)

/-- The template under test (the separated 2-hole spine). -/
def T : GuardedTemplate := spineTemplate demoSpine

/-- The output presented to the verifier: `data { { {`. -/
def out : List Value := [dataVal, braceVal, braceVal, braceVal]

/-- Its span decomposition: hole 0 ↦ `[data]`, the pinned delimiter `[{]`, hole 1 ↦ `[{, {]`. -/
def outSpans : List (List Value) := [[dataVal], [braceVal], [braceVal, braceVal]]

/-- Each span meets its segment's obligation: hole 0's span is brace-free (its `noBraceRE` guard
fires), the literal span IS the delimiter, hole 1's span is a DOUBLE brace admitted by `star any`. -/
theorem outSpans_ok : SpanOk T.segments outSpans := by
  refine ⟨?_, rfl, ?_, trivial⟩
  · exact derives_noBraceRE_of_nofire _ (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact leaf_braceP_data)
  · exact derives_star_any _

/-- `out` IS a member of the induced language — established through the span factorization, with NO
assignment in hand. This is the verifier's starting position. -/
theorem out_mem : out ∈ (guardedToGrammar T).language :=
  (mem_language_iff_spans T out).mpr ⟨outSpans, outSpans_ok, rfl⟩

/-- The template's hole ids are distinct. -/
theorem T_nodup : (holesOf T).Nodup := by decide

/-- The template is separated. -/
theorem T_separated : SeparatedTemplate T := ⟨demoSpine, rfl, demoSpine_separated⟩

/-- **The parse theorem firing**: from `out_mem` alone, guard-satisfying data rendering to `out`
EXISTS. -/
theorem out_parses : ∃ d : Nat → List Value, guardedSafe T d ∧ render T d = out :=
  parse_exists_distinct_holes T T_nodup out out_mem

/-- **The `∃!` firing**: exactly one hole-data vector produces `out`. -/
theorem out_parses_uniquely :
    ∃! ds : List (List Value),
      ∃ d : Nat → List Value, guardedSafe T d ∧ render T d = out ∧ (holesOf T).map d = ds :=
  separated_parse_exists_unique T T_separated T_nodup out out_mem

/-- The RECOVERED assignment, computed by the extractor (this is the witness the theorem produces). -/
def recovered : Nat → List Value := assign T.segments outSpans

/-- The recovered assignment really is guard-satisfying and really renders back to `out` — the two
halves of the existential, established on the concrete instance through the §2 lemmas (not merely
asserted by the existential). -/
theorem recovered_correct : guardedSafe T recovered ∧ render T recovered = out :=
  ⟨assign_guardedSafe T.segments outSpans outSpans_ok T_nodup,
   assign_render T.segments outSpans outSpans_ok T_nodup⟩

-- NON-VACUITY `#guard`s. `Value` carries no `DecidableEq` in-tree, so the recovered words are pinned
-- through the brace-predicate `leaf braceP` (`true` = `{`, `false` = `data`) — a faithful readout on
-- this 2-symbol demo alphabet — plus lengths and the verified matcher re-run on the RECOVERED data.
-- The hole ids the template names, in order:
#guard holesOf T == [0, 1]
-- The recovered per-hole data: hole 0 ↦ `[data]`, hole 1 ↦ `[{, {]` (a DOUBLE brace).
#guard (recovered 0).map (leaf braceP) == [false]
#guard (recovered 1).map (leaf braceP) == [true, true]
#guard (recovered 0).length == 1
#guard (recovered 1).length == 2
-- The recovered assignment renders back to the presented output `data { { {`:
#guard (render T recovered).map (leaf braceP) == [false, true, true, true]
#guard (render T recovered).length == 4
-- The guards, RE-RUN by the verified matcher on the RECOVERED data (the `guardedSafe` obligation):
#guard derives (recovered 0) noBraceRE
#guard derives (recovered 1) (PredRE.star PredRE.any)
-- ...and the recovery is DISCRIMINATING: hole 1's data would be REJECTED by hole 0's strict guard,
-- so `recovered` is not a constant/degenerate assignment.
#guard ! derives (recovered 1) noBraceRE
-- An id the template does not name gets the empty word (the `∃!` is over `holesOf T`, §4):
#guard (recovered 7).length == 0

end Demo

/-! ## §6 THE HONEST WALL — distinct hole ids are LOAD-BEARING for existence. -/

namespace Repeated

/-- A SEPARATED spine that names hole `0` TWICE: `hole 0 (noBraceRE) · lit[{] · hole 0 (star any)`.
Separation holds (hole 0's guard excludes the delimiter); distinctness FAILS. -/
def repSpine : SepSpine := .cons 0 noBraceRE braceVal (.last 0 (PredRE.star PredRE.any))

/-- The repeated-id template. -/
def repT : GuardedTemplate := spineTemplate repSpine

/-- It IS separated — so the wall is not about separation. -/
theorem repT_separated : SeparatedTemplate repT := ⟨repSpine, rfl, ⟨noBraceRE_excludes, trivial⟩⟩

/-- Its hole ids are `[0, 0]` — NOT `Nodup`. -/
theorem repT_not_nodup : ¬ (holesOf repT).Nodup := by decide

/-- The output `data {`: a language member (hole 0 ↦ `[data]`, delimiter `[{]`, hole 0 ↦ `[]`). -/
def repOut : List Value := [dataVal, braceVal]

theorem repOut_mem : repOut ∈ (guardedToGrammar repT).language :=
  (mem_language_iff_spans repT repOut).mpr
    ⟨[[dataVal], [braceVal], []],
     ⟨derives_noBraceRE_of_nofire _ (by
        intro b hb
        simp only [List.mem_singleton] at hb
        subst hb
        exact leaf_braceP_data), rfl, derives_star_any _, trivial⟩,
     rfl⟩

/-- **`nodup_is_load_bearing`** — the distinct-hole-id side-condition of `parse_exists_distinct_holes`
is NOT hygiene: dropping it makes the parse theorem FALSE. Here is a `SeparatedTemplate` and a member
of its language that NO assignment renders — guard-satisfying or otherwise. The template prints hole
`0` twice, so every render has length `2·|d 0| + 1`, always ODD; the exhibited language member has
length 2. The language lets the two spans of the repeated hole DIFFER; `render` cannot.

Together with `HandlebarsGuardedUniqueness.abutting_ambiguous` (separation is load-bearing for
UNIQUENESS) this pins both side-conditions of the `∃!` (§4) as necessary, each by a demonstrated
counterexample rather than by assertion. -/
theorem nodup_is_load_bearing :
    ∃ (T : GuardedTemplate) (output : List Value),
      SeparatedTemplate T ∧ output ∈ (guardedToGrammar T).language ∧
      ¬ ∃ d : Nat → List Value, guardedSafe T d ∧ render T d = output := by
  refine ⟨repT, repOut, repT_separated, repOut_mem, ?_⟩
  rintro ⟨d, -, hr⟩
  have hshape : render repT d = d 0 ++ braceVal :: d 0 := by
    simp only [repT, repSpine, render_spine_cons, render_spine_last]
  rw [hshape] at hr
  have hlen := congrArg List.length hr
  simp only [repOut, List.length_append, List.length_cons, List.length_nil] at hlen
  omega

end Repeated

/-! ## §7 Axiom hygiene. -/

#assert_axioms assign_guardedSafe
#assert_axioms assign_render
#assert_axioms parse_exists_distinct_holes
#assert_axioms separated_parse_unique_pointwise
#assert_axioms separated_parse_exists_unique
#assert_axioms Demo.out_parses
#assert_axioms Demo.out_parses_uniquely
#assert_axioms Demo.recovered_correct
#assert_axioms Repeated.nodup_is_load_bearing

/-! ## §8 What is STILL open (named, not `sorry`-ed).

  -- RESIDUAL (Tok-level parse): this closes the parse direction for the GUARDED framework
  -- (`guardedToGrammar`, alphabet `Value`). The committed 2-symbol formulation's residual
  -- (`Handlebars.lean` §9 `RESIDUAL (round_trip)`, over `handlebarsToGrammar` / `Tok`) is NOT
  -- discharged by transport: it needs the identification of `handlebarsToGrammar T` with
  -- `guardedToGrammar` of the `tokVal`-embedded template (the same identification
  -- `HandlebarsGuardedUniqueness` §9 names as its `HandlebarsUniqueness` tie). Separate slice.

  -- RESIDUAL (decidable recognizer): `parse_exists_distinct_holes` consumes a PROOF of membership.
  -- Turning `(T, output)` into that proof needs a decider for the guarded language — the composed
  -- span search (`derives` per hole span) — i.e. `HandlebarsGuardedUniqueness` §9's
  -- `SeparatedFormB` recognizer plus a span-splitting decision procedure. On the separated class
  -- the split is forced, so this is a real (and finite) follow-on, not an open problem.

  -- RESIDUAL (junction breakout, inherited): as everywhere in this family, `∈ language` is IN-SLOT
  -- confinement. A guard ending in a frame that abuts a literal can still form a cross-junction
  -- structure; the byte-level guarantee needs junction-aware guards.
-/

end Dregg2.Crypto.HandlebarsGuardedParse
