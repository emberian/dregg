/-
# Dregg2.Crypto.HandlebarsCompose — COMPOSITION: a hole filled by another template's proof.

`Handlebars.lean` proves generation soundness for ONE template `T` (safe rendering ⇒ language
member); `HandlebarsWitness.lean` MATERIALIZES that generation witness. This module is THE FIFTH
THING: **composition** — a template hole filled not by raw safe-data but by ANOTHER template's
proof-carrying output, and the two generation proofs NESTING.

The construction. Given an outer template `T`, a hole `h` of it, and an inner template `T'`, the
**combined grammar** `handlebarsCompose T h T'` is the disjoint union of both templates' grammars
(nonterminals `NT ⊕ NT`: outer on the left via `Sum.inl`, inner on the right via `Sum.inr`), with
hole `h`'s per-hole recognizer rules REMOVED and REPLACED by a single **bridge production**

    safeD h  →  inner.initial          (`Sum.inl (NT.safeD h) → Sum.inl? no — Sum.inr NT.start`)

so the outer hole `h` no longer derives raw safe-data; it derives the INNER template's whole
language. Every inner rule is injected through `Sum.inr`; every surviving outer rule (start + the
OTHER holes' recognizers) through `Sum.inl`.

The new transport lemma (`derives_lift`). A `Derives` in the INNER grammar lifts to a `Derives` in
the combined grammar by mapping inner nonterminals through the disjoint-union injection `Sum.inr`.
Its shape is copied from mathlib's reverse-closure block
(`Mathlib/Computability/ContextFreeGrammar.lean` `Derives.reverse`): a structural map on symbols
(`symMap`) that preserves `Rewrites`/`Produces`, folded over the `Derives` chain by induction.

The nesting-soundness theorem (`renderCompose_mem_language`). Rendering `T` with hole `h` filled by
the inner render `render T' d'` (and other holes by `d`) lands in the combined grammar's language:
the outer `start` fires, each surviving segment derives as before (`compose_state_derives`, the
compose-native twin of `safe_state_derives`), and at hole `h` the bridge fires and the INNER
generation proof `render_mem_language T' d'` is transported in through `derives_lift`. The two
generation witnesses nest into one.

Soundness direction ONLY. Parse-UNAMBIGUITY of the composed grammar (a language member decomposes
back into outer-structure + a unique inner witness) is the named wall — the §9 uniqueness residual
of `Handlebars.lean`, untouched here, and NOT `sorry`-ed.
-/
import Dregg2.Crypto.Handlebars
import Dregg2.Crypto.HandlebarsWitness
import Dregg2.Crypto.CfgCompact
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsCompose

open ContextFreeGrammar
open Dregg2.Crypto.Handlebars
open Dregg2.Crypto.CfgCompact

/-! ## §1 Symbol / rule injection along a nonterminal map — the transport machinery.

`symMap f` transports a symbol along a nonterminal map `f : N → N'` (terminals fixed, nonterminals
relabelled); `ruleMap f` transports a whole rule. These are the structural maps mathlib's reverse
block folds over a `Derives` chain — here the fold is `derives_lift`. -/

/-- Transport a symbol along a nonterminal relabelling `f`: terminals stay, nonterminals map. -/
def symMap {N N' : Type} (f : N → N') : Symbol Tok N → Symbol Tok N'
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (f n)

/-- Transport a rule along `f`: relabel its input nonterminal, `symMap`-relabel its output string. -/
def ruleMap {N N' : Type} (f : N → N') (r : ContextFreeRule Tok N) : ContextFreeRule Tok N' :=
  ⟨f r.input, r.output.map (symMap f)⟩

/-- A string of pure terminals is fixed by `symMap` (terminals never carry a nonterminal to relabel).
Used to see the inner render's terminal output land unchanged after transport through `Sum.inr`. -/
theorem map_terminal_symMap {N N' : Type} (f : N → N') (w : List Tok) :
    (w.map Symbol.terminal).map (symMap f) = w.map Symbol.terminal := by
  induction w with
  | nil => rfl
  | cons t ts ih => simp [symMap, ih]

/-- **`symMap` preserves `Rewrites`.** A one-step rewrite by `r` lifts to a one-step rewrite by
`ruleMap f r`, both sides `symMap f`-relabelled. Proof: transport the `p, q` split of `rewrites_iff`
(the shape of `Rewrites.reverse` in mathlib's reverse block). -/
theorem rewrites_lift {N N' : Type} (f : N → N') {r : ContextFreeRule Tok N}
    {u v : List (Symbol Tok N)} (hr : r.Rewrites u v) :
    (ruleMap f r).Rewrites (u.map (symMap f)) (v.map (symMap f)) := by
  rw [ContextFreeRule.rewrites_iff] at hr ⊢
  obtain ⟨p, q, hu, hv⟩ := hr
  refine ⟨p.map (symMap f), q.map (symMap f), ?_, ?_⟩
  · subst hu; simp [symMap, ruleMap]
  · subst hv; simp [ruleMap]

/-- **`symMap` preserves `Produces`** across grammars, given the transported rule stays a rule. -/
theorem produces_lift {g g' : ContextFreeGrammar Tok} (f : g.NT → g'.NT)
    (hmem : ∀ r ∈ g.rules, ruleMap f r ∈ g'.rules)
    {u v : List (Symbol Tok g.NT)} (h : g.Produces u v) :
    g'.Produces (u.map (symMap f)) (v.map (symMap f)) := by
  obtain ⟨r, hr, hrw⟩ := h
  exact ⟨ruleMap f r, hmem r hr, rewrites_lift f hrw⟩

/-- **THE TRANSPORT LEMMA — `derives_lift`.** A `Derives` in `g` lifts to a `Derives` in `g'` along a
nonterminal map `f` whose transported rules land in `g'`. This is the NT-injection + Derives-transport
the composition needs: the inner template's generation `Derives` lifts, through `Sum.inr`, into the
combined grammar. Structural fold over the `Derives` chain — the exact shape of mathlib's
`Derives.reverse` (`ContextFreeGrammar.lean` reverse block): `refl` at the base, each tail step
transported by `produces_lift`. -/
theorem derives_lift {g g' : ContextFreeGrammar Tok} (f : g.NT → g'.NT)
    (hmem : ∀ r ∈ g.rules, ruleMap f r ∈ g'.rules)
    {u v : List (Symbol Tok g.NT)} (h : g.Derives u v) :
    g'.Derives (u.map (symMap f)) (v.map (symMap f)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ orig ih => exact ih.trans_produces (produces_lift f hmem orig)

/-! ## §2 The combined grammar `handlebarsCompose`.

Nonterminals `NT ⊕ NT`: outer (`Sum.inl`), inner (`Sum.inr`). Rules: the outer start (mapped inl),
the bridge `safeD h → inner.initial`, every OTHER outer hole's recognizer (mapped inl, hole `h`
DROPPED), and every inner rule (mapped inr). -/

/-- Combined nonterminals: outer via `Sum.inl`, inner via `Sum.inr`. -/
abbrev CNT : Type := NT ⊕ NT

/-- **The bridge production** `safeD h → inner.initial`: the outer hole `h` derives the INNER
template's start nonterminal (hence its whole language) instead of raw safe-data. `inner.initial`
is `NT.start`, injected right via `Sum.inr`. -/
def bridgeRule (h : HoleId) : ContextFreeRule Tok CNT :=
  ⟨Sum.inl (NT.safeD h), [Symbol.nonterminal (Sum.inr NT.start)]⟩

/-- The surviving outer holes' recognizer rules (mapped `Sum.inl`), with hole `h`'s rules DROPPED
(replaced by the bridge). Emitting `[]` for `h` is the faithful removal. -/
def outerHoleRulesMapped (T : HandlebarsTemplate) (h : HoleId) : List (ContextFreeRule Tok CNT) :=
  (holesOf T).flatMap (fun g => if g = h then [] else (holeRules g).map (ruleMap Sum.inl))

/-- All combined rules: outer start (inl) :: bridge :: (surviving outer holes (inl) ++ inner (inr)). -/
def composeRuleList (T : HandlebarsTemplate) (h : HoleId) (T' : HandlebarsTemplate) :
    List (ContextFreeRule Tok CNT) :=
  ruleMap Sum.inl (startRule T)
    :: bridgeRule h
    :: (outerHoleRulesMapped T h ++ (allRules T').map (ruleMap Sum.inr))

/-- **`handlebarsCompose T h T'`** — the combined grammar: `T` with hole `h` filled by `T'`'s language.
Disjoint-union nonterminals, hole `h`'s recognizer replaced by the bridge onto the inner initial. -/
def handlebarsCompose (T : HandlebarsTemplate) (h : HoleId) (T' : HandlebarsTemplate) :
    ContextFreeGrammar Tok :=
  ⟨CNT, Sum.inl NT.start, (composeRuleList T h T').toFinset⟩

/-! ## §3 Rule-membership plumbing for the combined grammar. -/

/-- The outer start rule (mapped inl) is a rule of the combined grammar. -/
theorem start_rule_lifts {T : HandlebarsTemplate} {h : HoleId} {T' : HandlebarsTemplate} :
    ruleMap Sum.inl (startRule T) ∈ (handlebarsCompose T h T').rules :=
  List.mem_toFinset.mpr List.mem_cons_self

/-- The bridge production is a rule of the combined grammar. -/
theorem bridge_rule_lifts {T : HandlebarsTemplate} {h : HoleId} {T' : HandlebarsTemplate} :
    bridgeRule h ∈ (handlebarsCompose T h T').rules :=
  List.mem_toFinset.mpr (List.mem_cons_of_mem _ List.mem_cons_self)

/-- Every INNER rule, mapped through `Sum.inr`, is a rule of the combined grammar. This is the
membership side-condition `derives_lift` needs to transport the inner generation `Derives`. -/
theorem inner_rule_lifts {T : HandlebarsTemplate} {h : HoleId} {T' : HandlebarsTemplate} :
    ∀ (r : ContextFreeRule Tok NT), r ∈ (handlebarsToGrammar T').rules →
      ruleMap Sum.inr r ∈ (handlebarsCompose T h T').rules := by
  intro r hr
  apply List.mem_toFinset.mpr
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ ?_))
  exact List.mem_map.mpr ⟨r, List.mem_toFinset.mp hr, rfl⟩

/-- Every SURVIVING outer hole's rule (`g ≠ h`), mapped through `Sum.inl`, is a combined rule. -/
theorem outer_holeRule_lifts {T : HandlebarsTemplate} {h : HoleId} {T' : HandlebarsTemplate}
    {g : HoleId} (hg : g ∈ holesOf T) (hne : g ≠ h)
    {r : ContextFreeRule Tok NT} (hr : r ∈ holeRules g) :
    ruleMap Sum.inl r ∈ (handlebarsCompose T h T').rules := by
  apply List.mem_toFinset.mpr
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
  refine List.mem_flatMap.mpr ⟨g, hg, ?_⟩
  rw [if_neg hne]
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

/-! ## §4 The compose-native recognizer — surviving holes still derive their safe data.

`compose_state_derives` is the compose-grammar twin of `Handlebars.safe_state_derives`: for a
SURVIVING hole `g ≠ h`, safe data still derives from `Sum.inl (safeD g)` using the inl-mapped
recognizer rules. Identical recursion to the original, membership via `outer_holeRule_lifts`. -/

/-- One leftmost step in the combined grammar (compose twin of `Handlebars.prodStep`). -/
private theorem cprodStep {T : HandlebarsTemplate} {h : HoleId} {T' : HandlebarsTemplate}
    (r : ContextFreeRule Tok CNT) (hr : r ∈ (handlebarsCompose T h T').rules)
    {target : List (Symbol Tok (handlebarsCompose T h T').NT)}
    (hd : (handlebarsCompose T h T').Derives r.output target) :
    (handlebarsCompose T h T').Derives [Symbol.nonterminal r.input] target :=
  Produces.trans_derives ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩ hd

/-- **The surviving recognizer replays as a derivation.** For a surviving hole `g ≠ h`, any
`NoDoubleBrace` word derives from `Sum.inl (stNT g s)` in the combined grammar. Carbon copy of
`Handlebars.safe_state_derives` with the inl-injected rules. -/
theorem compose_state_derives {T : HandlebarsTemplate} {h : HoleId} {T' : HandlebarsTemplate}
    {g : HoleId} (hg : g ∈ holesOf T) (hne : g ≠ h) :
    (s : St) → (w : List Tok) → NoDoubleBrace w → (s = St.b → w.head? ≠ some Tok.brace) →
      (handlebarsCompose T h T').Derives
        [Symbol.nonterminal (Sum.inl (stNT g s))] (w.map Symbol.terminal)
  | St.d, [], _, _ =>
      cprodStep (ruleMap Sum.inl ⟨NT.safeD g, []⟩)
        (outer_holeRule_lifts hg hne (by simp [holeRules]))
        Relation.ReflTransGen.refl
  | St.b, [], _, _ =>
      cprodStep (ruleMap Sum.inl ⟨NT.safeB g, []⟩)
        (outer_holeRule_lifts hg hne (by simp [holeRules]))
        Relation.ReflTransGen.refl
  | St.d, Tok.data :: rest, hw, _ =>
      cprodStep (ruleMap Sum.inl ⟨NT.safeD g, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD g)]⟩)
        (outer_holeRule_lifts hg hne (by simp [holeRules]))
        ((compose_state_derives hg hne St.d rest hw.tail (by simp)).append_left [Symbol.terminal Tok.data])
  | St.b, Tok.data :: rest, hw, _ =>
      cprodStep (ruleMap Sum.inl ⟨NT.safeB g, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD g)]⟩)
        (outer_holeRule_lifts hg hne (by simp [holeRules]))
        ((compose_state_derives hg hne St.d rest hw.tail (by simp)).append_left [Symbol.terminal Tok.data])
  | St.d, Tok.brace :: rest, hw, _ =>
      cprodStep (ruleMap Sum.inl ⟨NT.safeD g, [Symbol.terminal Tok.brace, Symbol.nonterminal (NT.safeB g)]⟩)
        (outer_holeRule_lifts hg hne (by simp [holeRules]))
        ((compose_state_derives hg hne St.b rest hw.tail (fun _ => hw.no_brace_after_brace)).append_left
          [Symbol.terminal Tok.brace])
  | St.b, Tok.brace :: rest, _, hb =>
      absurd (show (Tok.brace :: rest).head? = some Tok.brace from rfl) (hb rfl)

/-! ## §5 The fill assignment and the composed render. -/

/-- Fill assignment: hole `h` gets `inner`, every other hole `k` gets `d k`. -/
def fillH (d : HoleId → List Tok) (h : HoleId) (inner : List Tok) : HoleId → List Tok :=
  fun k => if k = h then inner else d k

@[simp] theorem fillH_self (d : HoleId → List Tok) (h : HoleId) (inner : List Tok) :
    fillH d h inner h = inner := by simp [fillH]

theorem fillH_other (d : HoleId → List Tok) (h : HoleId) (inner : List Tok) {k : HoleId}
    (hk : k ≠ h) : fillH d h inner k = d k := by simp [fillH, hk]

/-- **`renderCompose T h T' d d'`** — the composed output: render `T` with hole `h` filled by the
inner render `render T' d'`, and other holes by `d`. The NESTED render. -/
def renderCompose (T : HandlebarsTemplate) (h : HoleId) (T' : HandlebarsTemplate)
    (d d' : HoleId → List Tok) : List Tok :=
  render T (fillH d h (render T' d'))

/-! ## §6 The bridge derivation — hole `h` derives the inner language (transport in action). -/

/-- **`bridge_derives`** — the outer hole `h` derives the inner template's rendered output: the
bridge fires (`safeD h → inner.initial`), then the INNER generation proof `render_mem_language T' d'`
is transported into the combined grammar through `derives_lift` along `Sum.inr`. The two proofs
NEST here. -/
theorem bridge_derives (T : HandlebarsTemplate) (h : HoleId) (T' : HandlebarsTemplate)
    (d' : HoleId → List Tok) (hsafe' : safe T' d') :
    (handlebarsCompose T h T').Derives
      [Symbol.nonterminal (Sum.inl (NT.safeD h))]
      ((render T' d').map Symbol.terminal) := by
  have hinner : (handlebarsToGrammar T').Derives
      [Symbol.nonterminal NT.start] ((render T' d').map Symbol.terminal) := by
    have hmem := render_mem_language T' d' hsafe'
    rwa [mem_language_iff] at hmem
  have hlift := derives_lift (g := handlebarsToGrammar T') (g' := handlebarsCompose T h T')
    Sum.inr inner_rule_lifts hinner
  replace hlift := (congrArg (fun z => (handlebarsCompose T h T').Derives
      (List.map (symMap Sum.inr) [Symbol.nonterminal NT.start]) z)
    (map_terminal_symMap Sum.inr (render T' d'))).mp hlift
  simp only [List.map_cons, List.map_nil, symMap] at hlift
  have hbridge : (handlebarsCompose T h T').Produces
      [Symbol.nonterminal (Sum.inl (NT.safeD h))] [Symbol.nonterminal (Sum.inr NT.start)] :=
    ⟨bridgeRule h, bridge_rule_lifts, ContextFreeRule.Rewrites.input_output⟩
  exact hbridge.trans_derives hlift

/-! ## §7 The composed body derivation — every segment, with hole `h` NESTED. -/

/-- **`compose_body_derives`** — the outer start's RHS (inl-mapped) derives the composed render:
literals fixed, surviving holes via `compose_state_derives`, hole `h` via `bridge_derives`. The
compose twin of `Handlebars.body_derives`, with the hole-`h` case swapped for the nested bridge. -/
theorem compose_body_derives (T : HandlebarsTemplate) (h : HoleId) (T' : HandlebarsTemplate)
    (d d' : HoleId → List Tok) (hsafe' : safe T' d') :
    ∀ (segs : List Segment),
      (∀ x, Segment.hole x ∈ segs → x ≠ h → NoDoubleBrace (d x)) →
      (∀ x, Segment.hole x ∈ segs → x ∈ holesOf T) →
      (handlebarsCompose T h T').Derives
        ((segs.flatMap segSymbols).map (symMap Sum.inl))
        ((segs.flatMap (renderSeg (fillH d h (render T' d')))).map Symbol.terminal)
  | [], _, _ => Relation.ReflTransGen.refl
  | seg :: rest, hsafe, hmem => by
      simp only [List.flatMap_cons, List.map_append]
      have ihrest := compose_body_derives T h T' d d' hsafe' rest
        (fun x hx hne => hsafe x (List.mem_cons_of_mem _ hx) hne)
        (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      have hhead : (handlebarsCompose T h T').Derives
          ((segSymbols seg).map (symMap Sum.inl))
          ((renderSeg (fillH d h (render T' d')) seg).map Symbol.terminal) := by
        cases seg with
        | lit text =>
            simp only [segSymbols, renderSeg]
            exact (congrArg (fun z => (handlebarsCompose T h T').Derives z (text.map Symbol.terminal))
              (map_terminal_symMap Sum.inl text)).mpr Relation.ReflTransGen.refl
        | hole g =>
            simp only [segSymbols, renderSeg, List.map_cons, List.map_nil, symMap]
            by_cases hgh : g = h
            · subst hgh
              rw [fillH_self]
              exact bridge_derives T g T' d' hsafe'
            · rw [fillH_other d h (render T' d') hgh]
              exact compose_state_derives (hmem g List.mem_cons_self) hgh St.d (d g)
                (hsafe g List.mem_cons_self hgh) (by simp)
      exact derives_append hhead ihrest

/-! ## §8 THE NESTING-SOUNDNESS THEOREM. -/

/-- **`renderCompose_mem_language`** — NESTING SOUNDNESS: the composed render lands in the combined
grammar's language. The outer `start` fires, then `compose_body_derives` walks the body — with hole
`h`'s chunk supplied by the INNER generation proof transported through `derives_lift`. The outer and
inner generation witnesses nest into a single derivation of the combined grammar.

Hypotheses: only the SURVIVING outer holes (`x ≠ h`) need safe data (`d h` is discarded — hole `h`
is filled by the inner render); the inner data `d'` must be safe for `T'`. -/
theorem renderCompose_mem_language (T : HandlebarsTemplate) (h : HoleId) (T' : HandlebarsTemplate)
    (d d' : HoleId → List Tok)
    (hsafe : ∀ x, Segment.hole x ∈ T.segments → x ≠ h → NoDoubleBrace (d x))
    (hsafe' : safe T' d') :
    renderCompose T h T' d d' ∈ (handlebarsCompose T h T').language := by
  rw [mem_language_iff]
  have hstep : (handlebarsCompose T h T').Produces
      [Symbol.nonterminal (handlebarsCompose T h T').initial]
      ((startSymbols T).map (symMap Sum.inl)) :=
    ⟨ruleMap Sum.inl (startRule T), start_rule_lifts, ContextFreeRule.Rewrites.input_output⟩
  refine hstep.single.trans ?_
  exact compose_body_derives T h T' d d' hsafe' T.segments hsafe (fun _ hx => hole_mem_holesOf hx)

/-- **`renderCompose_injectionFree`** — the nesting restated on `injectionFree`: the composed render
is injection-free for the combined grammar. Composition preserves the structural property. -/
theorem renderCompose_injectionFree (T : HandlebarsTemplate) (h : HoleId) (T' : HandlebarsTemplate)
    (d d' : HoleId → List Tok)
    (hsafe : ∀ x, Segment.hole x ∈ T.segments → x ≠ h → NoDoubleBrace (d x))
    (hsafe' : safe T' d') :
    renderCompose T h T' d d' ∈ (handlebarsCompose T h T').language :=
  renderCompose_mem_language T h T' d d' hsafe hsafe'

#assert_axioms derives_lift
#assert_axioms compose_state_derives
#assert_axioms bridge_derives
#assert_axioms renderCompose_mem_language

/-! ## §9 RESIDUAL — the materialized NESTED replay witness (stated, not proved, NOT `sorry`).

`HandlebarsWitness.renderRules_accepts` materializes the SINGLE-template generation witness as a
`CfgCompact.Replay` (a wire-form leftmost rule sequence). The composed analogue would emit the
NESTED rule sequence — the outer start, each surviving segment's rules, and at hole `h` the bridge
rule followed by the INNER template's `renderRules T' d'` sequence transported through `Sum.inr` —
and prove it REPLAYS to `renderCompose T h T' d d'`. Materializing it requires a `Replay`-transport
lemma (the pushdown-machine twin of `derives_lift`: relabel a `Replay`'s stack through `symMap Sum.inr`,
threading a continuation, membership via `inner_rule_lifts`) plus a compose-native `segs_replay`. That
witness-transport is heavy; the membership theorem above is the load-bearing soundness fact, so the
materialized nested certificate is recorded here rather than built:

  -- RESIDUAL (nested_replay): the composed leftmost rule sequence
  --   renderComposeRules T h T' d d' :=
  --     ruleMap Sum.inl (startRule T)
  --       :: (T.segments.flatMap (fun seg => match seg with
  --            | .lit _   => []
  --            | .hole g  => if g = h
  --                          then bridgeRule h :: (renderRules T' d').map (ruleMap Sum.inr)
  --                          else (stateRules g St.d (d g)).map (ruleMap Sum.inl)))
  -- replays to `renderCompose T h T' d d'` from the initial stack:
  --   renderCompose_accepts :
  --     (∀ x, Segment.hole x ∈ T.segments → x ≠ h → NoDoubleBrace (d x)) → safe T' d' →
  --       ReplayAccepts (handlebarsCompose T h T') (renderComposeRules T h T' d d')
  --         (renderCompose T h T' d d')
  -- Its proof: a `Replay`-transport of `renderRules_accepts T' d'` through `Sum.inr` (mirroring
  -- `derives_lift`) spliced under the bridge, folded over the segments by a compose `segs_replay`.

## §10 RESIDUAL — parse-UNAMBIGUITY of the composed grammar (THE NAMED WALL).

Soundness (safe nested render ⇒ combined-language member) is proved. The CONVERSE — that a member of
`handlebarsCompose T h T'`'s language decomposes UNIQUELY into (outer structure, a unique inner
witness at hole `h`, unique safe data at the other holes) — is the §9 uniqueness residual of
`Handlebars.lean`, now compounded by the two-level nesting (an inner ambiguity would surface as a
composed ambiguity). It is NOT addressed here and NOT `sorry`-ed; it remains the delimiter-guarded
leftmost-uniqueness argument named there.
-/

/-! ## §11 Non-vacuity — a concrete NESTED demo, generated and landed in the language. -/

namespace Demo

/-- Outer template `"[" ++ {{0}} ++ "]"` — a bracketed slot at hole `0` (the composition point). -/
def outerT : HandlebarsTemplate :=
  ⟨[Segment.lit [Tok.data], Segment.hole 0, Segment.lit [Tok.data]]⟩

/-- Inner template `"(" ++ {{1}} ++ ")"` — its own bracketed slot at hole `1`. -/
def innerT : HandlebarsTemplate :=
  ⟨[Segment.lit [Tok.data], Segment.hole 1, Segment.lit [Tok.data]]⟩

/-- Outer non-composition holes: none (hole `0` is the composition point), so `d` is empty. -/
def dOuter : HoleId → List Tok := fun _ => []

/-- Inner fill: hole `1` gets `"x{y"` (a single interior brace — SAFE, not a `{{` breakout). -/
def dInner : HoleId → List Tok
  | 1 => [Tok.data, Tok.brace, Tok.data]
  | _ => []

/-- The surviving outer holes are trivially safe (`dOuter` is empty everywhere). -/
theorem dOuter_safe_nonh :
    ∀ x, Segment.hole x ∈ outerT.segments → x ≠ 0 → NoDoubleBrace (dOuter x) :=
  fun _ _ _ => trivial

/-- The inner fill is safe for `innerT` (`dInner 1` has a lone interior brace; others empty). -/
theorem dInner_safe : safe innerT dInner := by
  intro k hmem
  cases k with
  | zero => trivial
  | succ n =>
      cases n with
      | zero => decide
      | succ _ => trivial

/-- **Non-vacuity of the nesting theorem** — the concrete NESTED output (`"[" ++ "(x{y)" ++ "]"`)
lands in the combined grammar's language, carrying a nested generation witness. A single interior
`{` inside the inner slot survives composition. -/
theorem demo_nested_injectionFree :
    renderCompose outerT 0 innerT dOuter dInner ∈ (handlebarsCompose outerT 0 innerT).language :=
  renderCompose_mem_language outerT 0 innerT dOuter dInner dOuter_safe_nonh dInner_safe

-- The composed bytes: outer `[`, then inner `(`, `x`, `{`, `y`, `)`, then outer `]` — 7 tokens.
#guard renderCompose outerT 0 innerT dOuter dInner
  = [Tok.data, Tok.data, Tok.data, Tok.brace, Tok.data, Tok.data, Tok.data]

#assert_axioms demo_nested_injectionFree

end Demo

end Dregg2.Crypto.HandlebarsCompose
