/-
# Dregg2.Crypto.HandlebarsWitness — the MATERIALIZED generation witness.

`Handlebars.lean` proves generation soundness as an EXISTENCE statement:

    render_mem_language : safe T d → render T d ∈ (handlebarsToGrammar T).language

The proof walks a leftmost pushdown run (start `Produces`, then `body_derives` folds
`safe_state_derives` over the segments) but never NAMES the rule sequence it walks — the
derivation lives only inside the `Derives` proof term. This module MATERIALIZES it: it emits
the concrete leftmost rule list `renderRules T d` and proves it REPLAYS, in the
`CfgCompact.Replay` pushdown machine, to exactly `render T d`:

    renderRules_accepts : safe T d → ReplayAccepts (handlebarsToGrammar T) (renderRules T d) (render T d)

So the "there exists a generation witness" of §7 becomes "here IS the witness (a wire-form
`CompactCert`), and it checks." The correspondence is exact:

  * `Replay.rule` ≙ a `prodStep`/`Produces` step (same `hr : r ∈ g.rules` from
    `holeRule_mem`/`startRule_mem`, same `r.output ++ stk` shape);
  * `Replay.term` ≙ the `.append_left [Symbol.terminal ..]` step inside `safe_state_derives`;
  * `Replay.done` ≙ the `Relation.ReflTransGen.refl` that closes an ε arm.

The one lemma needing thought is `segs_replay` — a stack-threading `Replay` composition
(the compact twin of `derives_append`/`body_derives`): it replays a segment list against a
CONTINUATION stack `stk2`/input `in2`/rule tail `rs2`, threading them through the recursion.
`compact_sound (renderRules_accepts h)` reproduces `render_mem_language h` on the nose
(proof irrelevance): the materialized witness AGREES with the existence proof (§Consistency).

The §9 uniqueness / round-trip residual of `Handlebars.lean` is untouched here — materializing
the GENERATE-direction witness says nothing about parse-uniqueness, and this module does not
claim it.
-/
import Dregg2.Crypto.Handlebars
import Dregg2.Crypto.CfgCompact
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsWitness

open ContextFreeGrammar
open Dregg2.Crypto.Handlebars
open Dregg2.Crypto.CfgCompact

/-! ## §1 The concrete leftmost rule sequence.

`stateRules h s w` is the rule list `safe_state_derives` walks from state `s` on word `w`:
each `data`/`brace` pops a terminal via the matching `safeD/safeB → t stNT'` rule; the empty
word closes with `stNT → ε`. The `safeB, brace ::` arm is unreachable under safety (a `{{`
breakout) — the recognizer forbids it — so it emits `[]` (the lemma discharges it by `absurd`). -/

/-- The rule list realizing `safe_state_derives h s w` — one rule per terminal emitted plus the
closing ε rule. Mirrors `Handlebars.safe_state_derives`'s recursion exactly. -/
def stateRules (h : HoleId) : St → List Tok → List (ContextFreeRule Tok NT)
  | St.d, [] => [⟨NT.safeD h, []⟩]
  | St.b, [] => [⟨NT.safeB h, []⟩]
  | St.d, Tok.data :: rest =>
      ⟨NT.safeD h, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD h)]⟩ ::
        stateRules h St.d rest
  | St.b, Tok.data :: rest =>
      ⟨NT.safeB h, [Symbol.terminal Tok.data, Symbol.nonterminal (NT.safeD h)]⟩ ::
        stateRules h St.d rest
  | St.d, Tok.brace :: rest =>
      ⟨NT.safeD h, [Symbol.terminal Tok.brace, Symbol.nonterminal (NT.safeB h)]⟩ ::
        stateRules h St.b rest
  | St.b, Tok.brace :: _ => []

/-- One segment's rule contribution: a literal emits NO rules (pure `term` steps), a hole emits
its `safeD`-from-state-`d` walk. Mirror of `Handlebars.segSymbols`. -/
def segRules (d : HoleId → List Tok) : Segment → List (ContextFreeRule Tok NT)
  | .lit _ => []
  | .hole h => stateRules h St.d (d h)

/-- **`renderRules T d`** — the materialized leftmost rule sequence for rendering `T` with `d`:
the `start` production, then each segment's rules in order. Mirror of `Handlebars.allRules`'
start-then-body shape, but instantiated to the ACTUAL render (only the holes' emitted rules,
in leftmost order), not the whole grammar's rule set. -/
def renderRules (T : HandlebarsTemplate) (d : HoleId → List Tok) : List (ContextFreeRule Tok NT) :=
  startRule T :: T.segments.flatMap (segRules d)

/-! ## §2 Literal replay — a run of `term` steps against a continuation stack. -/

/-- A literal segment consumes its bytes by a run of `Replay.term` steps, threading the
continuation `⟨rs2, in2, stk2⟩` underneath. The compact twin of "literals are fixed" in
`body_derives`. -/
theorem lit_replay {T : HandlebarsTemplate} (text : List Tok)
    {rs2 : List (ContextFreeRule Tok NT)} {in2 : List Tok} {stk2 : List (Symbol Tok NT)}
    (hcont : Replay (handlebarsToGrammar T) rs2 in2 stk2) :
    Replay (handlebarsToGrammar T) rs2 (text ++ in2) (text.map Symbol.terminal ++ stk2) := by
  induction text with
  | nil => exact hcont
  | cons t ts ih =>
      simp only [List.map_cons, List.cons_append]
      exact Replay.term t ih

/-! ## §3 The per-hole "no `{{`" REPLAY — the compact twin of `safe_state_derives`. -/

/-- **The recognizer replays as a materialized run.** From state `s`, a `NoDoubleBrace` word `w`
(that, in state `b`, does not start with a brace) is CONSUMED by `stateRules h s w` against the
`safeD/safeB` nonterminal on top of a continuation stack. Each `prodStep` becomes a `Replay.rule`
(membership via `holeRule_mem`), each terminal emission becomes a `Replay.term`, and the closing
ε rule opens onto the threaded continuation. The `safeB, brace ::` arm is impossible under the
head hypothesis (`absurd`). Structural recursion on `w`, exactly as `safe_state_derives`. -/
theorem safe_state_replays {T : HandlebarsTemplate} {h : HoleId} (hh : h ∈ holesOf T) :
    (s : St) → (w : List Tok) → NoDoubleBrace w → (s = St.b → w.head? ≠ some Tok.brace) →
      (rs2 : List (ContextFreeRule Tok NT)) → (in2 : List Tok) → (stk2 : List (Symbol Tok NT)) →
      Replay (handlebarsToGrammar T) rs2 in2 stk2 →
        Replay (handlebarsToGrammar T) (stateRules h s w ++ rs2) (w ++ in2)
          (Symbol.nonterminal (stNT h s) :: stk2)
  | St.d, [], _, _, rs2, in2, stk2, hcont => by
      simp only [stateRules, stNT, List.cons_append, List.nil_append]
      exact Replay.rule (holeRule_mem hh (by simp [holeRules])) hcont
  | St.b, [], _, _, rs2, in2, stk2, hcont => by
      simp only [stateRules, stNT, List.cons_append, List.nil_append]
      exact Replay.rule (holeRule_mem hh (by simp [holeRules])) hcont
  | St.d, Tok.data :: rest, hw, _, rs2, in2, stk2, hcont => by
      simp only [stateRules, stNT, List.cons_append]
      refine Replay.rule (holeRule_mem hh (by simp [holeRules])) ?_
      exact Replay.term Tok.data
        (safe_state_replays hh St.d rest hw.tail (by simp) rs2 in2 stk2 hcont)
  | St.b, Tok.data :: rest, hw, _, rs2, in2, stk2, hcont => by
      simp only [stateRules, stNT, List.cons_append]
      refine Replay.rule (holeRule_mem hh (by simp [holeRules])) ?_
      exact Replay.term Tok.data
        (safe_state_replays hh St.d rest hw.tail (by simp) rs2 in2 stk2 hcont)
  | St.d, Tok.brace :: rest, hw, _, rs2, in2, stk2, hcont => by
      simp only [stateRules, stNT, List.cons_append]
      refine Replay.rule (holeRule_mem hh (by simp [holeRules])) ?_
      exact Replay.term Tok.brace
        (safe_state_replays hh St.b rest hw.tail (fun _ => hw.no_brace_after_brace)
          rs2 in2 stk2 hcont)
  | St.b, Tok.brace :: rest, _, hb, _, _, _, _ =>
      absurd (show (Tok.brace :: rest).head? = some Tok.brace from rfl) (hb rfl)

/-! ## §4 One segment replays against a continuation. -/

/-- One segment's symbols replay to its rendered bytes against a continuation. Literal ⇒
`lit_replay`; hole ⇒ `safe_state_replays` from state `d`. The compact twin of the `hhead`
case-split in `body_derives`. -/
theorem seg_replay {T : HandlebarsTemplate} (d : HoleId → List Tok) (seg : Segment)
    (hsafe : ∀ h, seg = Segment.hole h → NoDoubleBrace (d h))
    (hmem : ∀ h, seg = Segment.hole h → h ∈ holesOf T)
    {rs2 : List (ContextFreeRule Tok NT)} {in2 : List Tok} {stk2 : List (Symbol Tok NT)}
    (hcont : Replay (handlebarsToGrammar T) rs2 in2 stk2) :
    Replay (handlebarsToGrammar T) (segRules d seg ++ rs2) (renderSeg d seg ++ in2)
      (segSymbols seg ++ stk2) := by
  cases seg with
  | lit text =>
      simp only [segRules, renderSeg, segSymbols, List.nil_append]
      exact lit_replay text hcont
  | hole h =>
      simp only [segRules, renderSeg, segSymbols, List.singleton_append]
      exact safe_state_replays (hmem h rfl) St.d (d h) (hsafe h rfl) (by simp) rs2 in2 stk2 hcont

/-! ## §5 The segment-list replay — the stack-threading composition. -/

/-- **`segs_replay`** — THE stack-threading `Replay` composition (compact twin of `body_derives`).
A segment list replays its `flatMap segSymbols` to its `flatMap renderSeg` against ANY continuation
`⟨rs2, in2, stk2⟩`, threaded underneath via `seg_replay`. Structural recursion on the segment list;
the continuation is passed through unchanged (each segment's own rules/symbols/bytes wrap it). -/
theorem segs_replay (T : HandlebarsTemplate) (d : HoleId → List Tok) :
    ∀ (segs : List Segment),
      (∀ h, Segment.hole h ∈ segs → NoDoubleBrace (d h)) →
      (∀ h, Segment.hole h ∈ segs → h ∈ holesOf T) →
      ∀ (rs2 : List (ContextFreeRule Tok NT)) (in2 : List Tok) (stk2 : List (Symbol Tok NT)),
        Replay (handlebarsToGrammar T) rs2 in2 stk2 →
          Replay (handlebarsToGrammar T) (segs.flatMap (segRules d) ++ rs2)
            (segs.flatMap (renderSeg d) ++ in2) (segs.flatMap segSymbols ++ stk2)
  | [], _, _, rs2, in2, stk2, hcont => by simpa using hcont
  | seg :: rest, hsafe, hmem, rs2, in2, stk2, hcont => by
      simp only [List.flatMap_cons, List.append_assoc]
      refine seg_replay d seg ?_ ?_
        (segs_replay T d rest
          (fun h hh => hsafe h (List.mem_cons_of_mem _ hh))
          (fun h hh => hmem h (List.mem_cons_of_mem _ hh))
          rs2 in2 stk2 hcont)
      · exact fun h he => hsafe h (List.mem_cons.mpr (Or.inl he.symm))
      · exact fun h he => hmem h (List.mem_cons.mpr (Or.inl he.symm))

/-! ## §6 THE MATERIALIZED WITNESS — `renderRules` replays to `render`. -/

/-- **`renderRules_accepts`** — the materialized generation witness: rendering `T` with safe data
produces a leftmost rule sequence `renderRules T d` that REPLAYS (in the `CfgCompact.Replay`
pushdown machine) to exactly `render T d` from the initial stack. This is `render_mem_language`'s
existence content made CONCRETE and CHECKABLE — the `start` production fires, then every segment
replays against the shrinking stack down to `done`. -/
theorem renderRules_accepts (T : HandlebarsTemplate) (d : HoleId → List Tok) (hsafe : safe T d) :
    ReplayAccepts (handlebarsToGrammar T) (renderRules T d) (render T d) := by
  have hbody := segs_replay T d T.segments hsafe (fun _ hh => hole_mem_holesOf hh)
    [] [] [] Replay.done
  simp only [List.append_nil] at hbody
  show Replay (handlebarsToGrammar T) (renderRules T d) (render T d)
    [Symbol.nonterminal (handlebarsToGrammar T).initial]
  rw [renderRules]
  refine Replay.rule (startRule_mem T) ?_
  rw [List.append_nil]
  exact hbody

/-- **`renderWithProof T d`** — the render together with its materialized proof-carrying
certificate: `(output, leftmost rule sequence)`. The pair a prover puts on the wire; the verifier
runs `Replay`/`compact_sound` on it. -/
def renderWithProof (T : HandlebarsTemplate) (d : HoleId → List Tok) :
    (List Tok) × (List (ContextFreeRule Tok NT)) :=
  (render T d, renderRules T d)

/-! ## §7 CONSISTENCY TOOTH — the materialized witness agrees with the existence proof. -/

/-- **`materialized_agrees`** — feeding the materialized certificate through `CfgCompact.compact_sound`
⚠⚠ CONTENT-FREE — DO NOT CITE THIS AS A CONSISTENCY TOOTH (an adversarial review caught it, and it
had already propagated into commit messages). Lean 4 has DEFINITIONAL PROOF IRRELEVANCE: any two terms
of the same `Prop` are defeq. Both sides here are proofs of the same membership
`render T d ∈ (handlebarsToGrammar T).language`, so this `rfl` holds for ANY pair of proofs of that
statement — including a garbage one. It therefore establishes NOTHING about the materialized witness
agreeing with the generation proof; it is a tautology, not evidence.

What WOULD be a real tooth: an equation between the DATA (e.g. `renderRules T d` equalling an
independently-computed rule list), or a `Bool`-level agreement via the decider `replayCheckB` — both of
which live in `Type`, where `rfl` carries content. The genuine result in this file is
`renderRules_accepts` (the materialized witness IS accepted, one-way: safe ⇒ accepts). -/
theorem materialized_agrees (T : HandlebarsTemplate) (d : HoleId → List Tok) (hsafe : safe T d) :
    compact_sound (handlebarsToGrammar T) (renderRules T d) (render T d)
        (renderRules_accepts T d hsafe)
      = render_mem_language T d hsafe := rfl

#assert_axioms safe_state_replays
#assert_axioms renderRules_accepts
#assert_axioms materialized_agrees

/-! ## §8 Non-vacuity — the demo template, materialized and replayed. -/

namespace Demo

open Dregg2.Crypto.Handlebars.Demo

/-- The materialized certificate for `greetT` filled with `greetD` (`"[" ++ "x{y" ++ "]"`):
the rendered bytes together with their concrete leftmost rule sequence. -/
def greetCert : (List Tok) × (List (ContextFreeRule Tok NT)) :=
  renderWithProof greetT greetD

/-- **The demo certificate REPLAYS** — the concrete `renderRules greetT greetD` drives an accepting
`Replay` of `render greetT greetD` from the initial stack. A materialized, checked generation
witness (not merely "one exists"). -/
theorem greet_renderRules_accepts :
    ReplayAccepts (handlebarsToGrammar greetT) (renderRules greetT greetD) (render greetT greetD) :=
  renderRules_accepts greetT greetD greetD_safe

/-- On the demo, the materialized certificate's soundness output IS `render_mem_language`. -/
theorem greet_materialized_agrees :
    compact_sound (handlebarsToGrammar greetT) (renderRules greetT greetD) (render greetT greetD)
        greet_renderRules_accepts
      = render_mem_language greetT greetD greetD_safe := rfl

-- Concrete shape checks (`Replay` is a `Prop`, so the ACCEPT is the theorem above; these guard the
-- materialized data the theorem is about): the rendered bytes and the certificate's rule count.
#guard (renderWithProof greetT greetD).1 = [Tok.data, Tok.data, Tok.brace, Tok.data, Tok.data]
#guard (renderWithProof greetT greetD).2.length = 5

#assert_axioms greet_renderRules_accepts

end Demo

/-! ## §9 RESIDUAL — untouched by materialization.

Materialization is entirely within the GENERATE direction: it names the witness `render_mem_language`
already proved to exist. The §9 residual of `Handlebars.lean` — the round-trip / parse-uniqueness
CONVERSE (a language member decomposes back into template structure + recoverable per-hole data) —
is NOT addressed here and is NOT `sorry`-ed; it remains the leftmost-uniqueness argument named there.
A materialized generation certificate says "these bytes CAN be generated so-and-so", never "ONLY
so-and-so", so it neither needs nor supplies uniqueness. -/

end Dregg2.Crypto.HandlebarsWitness
