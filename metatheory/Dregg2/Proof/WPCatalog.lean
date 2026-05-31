/-
# Dregg2.Proof.WPCatalog — the userspace-verification loop, closed end-to-end and automated.

The pieces existed separately:
  * the `dregg_program { … }` eDSL (`Dregg2/DSL.lean`) — a readable block → a verified
    `RecordProgram`;
  * the VCG / WP program logic (`Dregg2/Proof/WP.lean`) — `vcg`/`CellSpec`/`vcg_run_sound`, the
    machine that lifts a discharged VC set to a whole-run safety theorem;
  * the `discharge` guard-seam tactic + `dregg_auto` (`Dregg2/Catalog.lean`, `Dregg2/Tactics.lean`)
    and the per-constraint `admits_*` lemmas (`Dregg2/Exec/RecordCellLive.lean`).

This module WIRES THEM TOGETHER into a single demonstrated pipeline:

  eDSL/catalog program  →  `vcg program method spec`  →  `vcg_discharge`  →  `vcg_run_sound`
                                                                          →  a run-invariant theorem.

The headline (`ledgerSM`) is a **multi-field state machine** authored via `dregg_program { … }`,
carrying THREE simultaneous obligations: a **conservation** invariant
(`escrowed + paidOut = deposit₀`), a **monotonic** sequence counter (`seq` never decreases), and an
**allowed-transitions** guard on `status` (the bounded `Open→Settling→Settled` lifecycle). The VCG
generates its obligations; `vcg_discharge` closes the auto-closable VC classes; `vcg_run_sound`
yields the capstone — `inv` holds along EVERY run of the cell.

## The automation honesty rail (`Conserve.lean` / `Catalog.lean` template)
`vcg_discharge` is fail-loud: the real work is wrapped in `first | <real>; done | fail "…"`, the
`done` is load-bearing (no half-open VC may masquerade as progress), and it is negative-tested with
`fail_if_success` (it provably cannot fake-close). The capstone + key lemmas are `#assert_axioms`-pinned.

No `axiom`/`admit`/`native_decide`/`sorry`.
-/
import Dregg2.Proof.WP
import Dregg2.DSL
import Dregg2.Catalog
import Dregg2.Tactics

namespace Dregg2.Proof.WPCatalog

open Dregg2.Exec Dregg2.Exec.RecordCell Dregg2.Boundary Dregg2.Execution
open Dregg2.Proof.WP

/-! ## §1 — `vcg_discharge`: the VC-class closer (fail-loud).

The `vcg` emits four VC classes (`VC_preserve`/`VC_stayput`/`VC_init`/`VC_post`). Three of them
(`stayput`/`init`/`post`) are structurally trivial whenever `pre = inv = post` (the common case):
they close by `intro`/`exact`. The load-bearing class is **`VC_preserve`** — "the gate firing
preserves `inv`" — whose discharge composes:

  1. `intro old new hinv hadm` — open the obligation;
  2. open the predicate-gate seam: `admits (.predicate cs) … = (cs.all …)`, split the `List.all`
     conjunction into one Boolean fact per constraint (the `discharge`-analog at the RecordProgram
     tier — `admits_predicate` + `List.all_cons`/`List.all_nil`, then `evalConstraint`/`evalSimple`);
  3. close the leaves: each constraint's post-state fact is now a decidable Boolean equation
     (`==`/`decide`), reconciled with the invariant by `dregg_auto`/`decide`/`omega` and the
     `@[simp] admits_sumEquals`-style content facts.

`vcg_discharge` (the unified opener + closer) is defined in §3.5, AFTER the worked program +
specs — Lean macro hygiene resolves the spec/program identifiers named in the macro body at the
macro's *definition* site, so they must already exist when the macro is declared. It is fail-loud:
the seam-opening `simp only` errors on no progress (a non-VC goal falls straight to the `fail`
branch), and every closer arm ends in `done` so a half-open VC can never masquerade as success. -/

/-! ## §2 — The worked program: a multi-field ledger state machine, authored via the eDSL.

`ledgerSM` is a single `.predicate` program (so `admits_sumEquals` and the `recReplay_*`
keystones apply to *this exact term*) carrying THREE simultaneous constraints:

  * **conservation** — `sum [escrowed, paidOut] = 100` (the escrowed funds plus the paid-out funds
    always total the original deposit of 100);
  * **monotonic counter** — `monotonic seq` (the settlement sequence number never decreases);
  * **allowed transitions** — `status : 0 => 1` (the lifecycle edge Open(0)→Settling(1) — a
    bounded state machine guard; the DSL's `allowedTransitions` atom).

Authored with `dregg_program { … }`, it elaborates to exactly the catalog `.predicate` term. The
three constraints bind SIMULTANEOUSLY (a `.predicate` ANDs them), so an admitted turn must conserve,
tick `seq` non-decreasing, AND take a legal `status` edge — a genuine multi-field state machine. -/

/-- The ledger state machine, WRITTEN IN THE eDSL. A single `invariant { … }` block ⇒ a
`.predicate` program over the three constraints (conservation + monotonic counter + allowed-edge
guard). -/
def ledgerSM : RecordProgram := dregg_program {
  invariant {
    sum [escrowed, paidOut] = 100 ,
    monotonic seq ,
    status : 0 => 1
  }
}

/-- **`ledgerSM` elaborates to exactly the expected catalog `.predicate` term — PROVED by `rfl`.**
The eDSL surface IS the verified term: `recReplay_preserves_sumEquals`/`recCexec_attests` apply to
*this* program with no codegen gap. -/
theorem ledgerSM_eq_expected :
    ledgerSM = RecordProgram.predicate
      [ .sumEquals ["escrowed", "paidOut"] 100,
        .simple (.monotonic "seq"),
        .allowedTransitions "status" [(0, 1)] ] := rfl

#assert_axioms ledgerSM_eq_expected

/-- The catalog constraint list of `ledgerSM` (so `admits_sumEquals`'s `cs` is exactly this). -/
def ledgerCs : List StateConstraint :=
  [ .sumEquals ["escrowed", "paidOut"] 100,
    .simple (.monotonic "seq"),
    .allowedTransitions "status" [(0, 1)] ]

theorem ledgerSM_is_predicate : ledgerSM = .predicate ledgerCs := rfl

/-! ## §3 — The spec: the conjunctive invariant the VCG must preserve.

`inv` is the conjunction of the three post-state facts the program enforces:
  * `escrowed + paidOut = 100` (conservation);
  * `seq` is present (the monotonic field exists — the *run-level* monotone fact `seq ≥ n₀` is the
    counter half, see `ledgerCounterSpec` below);
  * `status ∈ {1, 2}` once we have moved off Open — i.e. the lifecycle stays inside the bounded set.

For the conservation+lifecycle invariant we take the cleanly-preservable form: `inv` =
"conservation holds" (the headline falsifiable invariant; the monotone/transition constraints are
*relational* gates whose run-level consequences are the `ledgerCounter` fragment). -/

/-- The ledger conservation spec: `inv := escrowed + paidOut = 100`, with `pre = inv = post`. The
conservation invariant is a pure post-state fact, so VC class 1 closes by `admits_sumEquals`. -/
def ledgerSpec : CellSpec where
  pre  := fun v => sumScalars v ["escrowed", "paidOut"] = some 100
  post := fun v => sumScalars v ["escrowed", "paidOut"] = some 100
  inv  := fun v => sumScalars v ["escrowed", "paidOut"] = some 100

/-- The counter spec over `ledgerSM`'s `seq` field: `inv := seq ≥ n₀` (the monotonic-counter
fragment of the SAME program; see §5). -/
def ledgerCounterSpec (n₀ : Int) : CellSpec where
  pre  := fun v => ∃ c, v.scalar "seq" = some c ∧ n₀ ≤ c
  post := fun v => ∃ c, v.scalar "seq" = some c ∧ n₀ ≤ c
  inv  := fun v => ∃ c, v.scalar "seq" = some c ∧ n₀ ≤ c

/-- A deliberately-FALSE spec used in the §6 honesty-rail negative test: it demands the post-state
`escrowed = 999`, which the conservation gate does NOT imply, so its `VC_preserve` is unprovable. -/
def badSpec : CellSpec where
  pre  := fun v => v.scalar "escrowed" = some 999
  post := fun v => v.scalar "escrowed" = some 999
  inv  := fun v => v.scalar "escrowed" = some 999

/-! ## §3.5 — `vcg_discharge`: the VC-class closer (fail-loud).

Defined here, after the program + specs, so the identifiers the macro body names (`ledgerSM`,
`ledgerSpec`, `ledgerCounterSpec`, `badSpec`, `evalSimple_monotonic_iff`) are in scope at the
macro's definition site (Lean macro hygiene resolves them there, not at the use site). -/

/-- **`evalSimple_monotonic_iff` (PROVED)** — the monotone constraint's `evalSimple` as a genuine
`Int` inequality, WITHOUT naming the `private` `intLe` (we use `of_decide_eq_true`/`decide_eq_true`,
which see through `intLe a b ≡ decide (a ≤ b)` by defeq). This is the one content lemma the
relational VC class needs as a simp rule so the gate `monotonic seq` reduces to `old.seq ≤ new.seq`
in `vcg_discharge`. (The conservation class needs no such lemma — `sumEquals` is a post-state `==`.) -/
theorem evalSimple_monotonic_iff (f : FieldName) (o n : Value) :
    evalSimple (.monotonic f) o n = true ↔
      ∃ a b, o.scalar f = some a ∧ n.scalar f = some b ∧ a ≤ b := by
  simp only [evalSimple]
  cases ho : o.scalar f with
  | none => simp
  | some a =>
      cases hn : n.scalar f with
      | none => simp
      | some b =>
          simp only [Option.some.injEq]
          exact ⟨fun h => ⟨a, b, rfl, rfl, of_decide_eq_true h⟩,
                 fun ⟨a', b', ha, hb, hab⟩ => by subst ha; subst hb; exact decide_eq_true hab⟩

#assert_axioms evalSimple_monotonic_iff

/-- **`vcg_discharge`** — the end-to-end VC closer behind the fail-loud rail.

It `intro`s the universally-quantified VC, opens the predicate-gate seam (unfold the spec + `VC_*`,
`admits_predicate` to expose `cs.all`, split the `List.all`/`&&` into one fact per constraint,
`evalSimple_monotonic_iff` to turn the monotone gate into an inequality), then closes:
  * the **conservation class** (`sumEquals`, post-state only) by `assumption`/`simp_all` — the leaf
    `Σ new = c` IS the goal;
  * the **relational class** (`monotonic`, old-vs-new) by destructuring the monotone witness + the
    invariant and chaining `n₀ ≤ old ≤ new` via `omega`.

HONESTY RAIL: the whole body is `first | (…; done) | fail "…"`. The seam-opening `simp only … at *`
ERRORS ON NO PROGRESS, so on a goal that is not a `VC_preserve` obligation `vcg_discharge` falls
straight to the `fail` branch — it cannot fake progress. Every inner closer arm ends in `done`
(`(simp_all; done)`, the relational arm + the outer `done`), so a VC whose leaf is genuinely false
(the §6 `badSpec`) leaves that leaf OPEN, every arm errors, and `vcg_discharge` FAILS LOUDLY rather
than reporting a half-closed VC as success. Negative-tested by `fail_if_success` in §6. -/
macro "vcg_discharge" : tactic =>
  `(tactic| first
    | (-- open every universally-quantified VC obligation (NB: `old`/`new` are reserved DSL
       --   tokens in this file, so we name the states `vo`/`vn`)
       (try intro vo vn hinv hadm)
       -- open the predicate-gate seam (errors → `fail` on a goal with no VC structure)
       simp only [VC_preserve, CellSpec.inv, ledgerSpec, ledgerCounterSpec, badSpec, ledgerSM,
         admits_predicate, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
         evalConstraint, evalSimple_monotonic_iff, beq_iff_eq] at *
       -- close the leaves; each arm fully closes (`done`) or errors — none may fake progress
       first
         | done
         | assumption
         | (simp_all; done)
         | (-- relational class: destructure the monotone witness + the inv, rebuild + `omega`
            obtain ⟨_hsum, ⟨_wa, wb, hoa, hnb, _hab⟩, _hst⟩ := hadm
            obtain ⟨_wc, hc, _hle⟩ := hinv
            refine ⟨wb, hnb, ?_⟩
            rw [hoa, Option.some.injEq] at hc
            omega)
       -- load-bearing: no residual VC leaf may survive masquerading as progress
       done)
    | fail "vcg_discharge: no VC obligation to open (or a leaf was left open) — \
        is this a `vcg`/`VC_preserve` goal, and are its invariant facts present?")

/-! ## §4 — VCG → discharge → run-soundness, AUTOMATED.

`vcg ledgerSM 0 ledgerSpec` generates the four VC classes. We discharge them: VC class 1 by
`vcg_discharge` (which opens the predicate-gate seam and reads the conservation leaf back), VC
classes 2/3/4 trivially (`pre = inv = post`). The capstone is `vcg_run_sound`. -/

/-- **`ledger_VC_preserve` (PROVED — closed by `vcg_discharge`).** VC class 1 for the ledger SM:
whenever `ledgerSM` admits `(old, new)`, the conservation `escrowed + paidOut = 100` is preserved.
The automation opens the predicate gate, reads the `sumEquals` leaf, and closes — the conservation
constraint pins `new`'s sum regardless of `old`. THIS IS THE AUTOMATION WORKING: no hand proof. -/
theorem ledger_VC_preserve :
    VC_preserve ledgerSM 0 ledgerSpec := by
  vcg_discharge

/-- **`ledgerVCs` (PROVED)** — the full discharged VC set for the ledger SM: VC class 1 by
`ledger_VC_preserve` (automated); classes 2/3/4 trivial (`pre = inv = post`). -/
theorem ledgerVCs : vcg ledgerSM 0 ledgerSpec :=
  ⟨ledger_VC_preserve, VC_stayput_trivial _, fun _ h => h, fun _ h => h⟩

/-- **`ledger_run_sound` (THE CAPSTONE — PROVED via the automated pipeline).** For the
eDSL-authored `ledgerSM` program, the conservation invariant `escrowed + paidOut = 100` holds at
EVERY reachable state of the cell's whole run, given it holds at the start. Produced end-to-end:
`dregg_program {…}` → `vcg` → `vcg_discharge` → `vcg_run_sound`. The demonstrated userspace-
verification loop. -/
theorem ledger_run_sound
    {s s' : RecChained}
    (hprogInv : ∀ x : RecChained, x.program = ledgerSM)
    (hmethodInv : ∀ x : RecChained, x.method = 0)
    (hrun : Execution.Run (inducedSystem recordCell) s s')
    (h0 : sumScalars s.value ["escrowed", "paidOut"] = some 100) :
    sumScalars s'.value ["escrowed", "paidOut"] = some 100 :=
  (vcg_run_sound ledgerSM ledgerSpec hprogInv hmethodInv ledgerVCs hrun h0).1

#assert_axioms ledger_VC_preserve
#assert_axioms ledgerVCs
#assert_axioms ledger_run_sound

/-! ## §5 — The monotonic-counter fragment of the SAME program, automated.

The `monotonic seq` constraint of `ledgerSM` gives a *second* run-invariant: `seq ≥ n₀` once it
holds at the start. We spec it separately (`inv := seq ≥ n₀`) and discharge VC class 1 by the same
`vcg_discharge` opener — the monotone leaf `old.seq ≤ new.seq` combines with `n₀ ≤ old.seq` by
`omega`. This shows the automation handles the *relational* (old-vs-new) constraint class too, not
just the post-state-only conservation class. (`ledgerCounterSpec` is defined in §3.) -/

/-- **`ledgerCounter_VC_preserve` (PROVED — closed by `vcg_discharge`).** VC class 1 for the
`seq ≥ n₀` invariant: the monotone gate gives `old.seq ≤ new.seq`, and `n₀ ≤ old.seq` (the
invariant) chains to `n₀ ≤ new.seq` by `omega`. The relational-constraint automation. -/
theorem ledgerCounter_VC_preserve (n₀ : Int) :
    VC_preserve ledgerSM 0 (ledgerCounterSpec n₀) := by
  vcg_discharge

/-- **`ledgerCounterVCs` (PROVED)** — full discharged VC set for the `seq ≥ n₀` invariant. -/
theorem ledgerCounterVCs (n₀ : Int) : vcg ledgerSM 0 (ledgerCounterSpec n₀) :=
  ⟨ledgerCounter_VC_preserve n₀, VC_stayput_trivial _, fun _ h => h, fun _ h => h⟩

/-- **`ledgerCounter_run_sound` (PROVED — the counter-fragment capstone).** For `ledgerSM`,
`seq ≥ n₀` holds at every reachable state of the whole run. The monotonic-counter half of the
multi-field invariant, produced by the same automated pipeline. -/
theorem ledgerCounter_run_sound (n₀ : Int)
    {s s' : RecChained}
    (hprogInv : ∀ x : RecChained, x.program = ledgerSM)
    (hmethodInv : ∀ x : RecChained, x.method = 0)
    (hrun : Execution.Run (inducedSystem recordCell) s s')
    (h0 : ∃ c, s.value.scalar "seq" = some c ∧ n₀ ≤ c) :
    ∃ c, s'.value.scalar "seq" = some c ∧ n₀ ≤ c :=
  (vcg_run_sound ledgerSM (ledgerCounterSpec n₀) hprogInv hmethodInv
    (ledgerCounterVCs n₀) hrun h0).1

#assert_axioms ledgerCounter_VC_preserve
#assert_axioms ledgerCounterVCs
#assert_axioms ledgerCounter_run_sound

/-! ## §6 — HONESTY-RAIL negative tests: `vcg_discharge` provably cannot fake-close.

The fail-loud rail is build-checked: if `vcg_discharge` ever silently "succeeded" on a non-VC goal
or fabricated a false leaf, these `example`s would fail to compile. -/

/-- Negative test 1: on a goal with NO VC / `admits` structure, `vcg_discharge` must FAIL LOUDLY
(the seam-opening `simp only … at *` makes no progress ⇒ the first arm errors ⇒ the `fail` branch fires).
`fail_if_success` turns that required failure into a passing regression. -/
example (n : Nat) (_h : n = 1) : True := by
  fail_if_success
    (have : n + 2 = 3 := by vcg_discharge)
  trivial

/-- Negative test 2: a `VC_preserve` for a GENUINELY-FALSE invariant cannot be closed —
`vcg_discharge` opens the gate, reduces to a false leaf, and stops (never fabricating it). Here the
spec demands the post-state `escrowed = 999` which the conservation gate does NOT imply, so the VC
is unprovable and `vcg_discharge` fails (asserted via `fail_if_success`). `badSpec` is defined in §3. -/
example : True := by
  fail_if_success
    (have : VC_preserve ledgerSM 0 badSpec := by vcg_discharge)
  trivial

/-! ## §7 — `#eval` discriminating checks (fail-closed: admit the good, reject the bad).

The VCG runs over the EXACT `ledgerSM` term the eDSL produced. Its admissibility gate must fire on
a well-formed lifecycle move and reject every violation — so VC class 1 is about a genuinely-gated
arrow, not a vacuous one. (Method is irrelevant for a `.predicate` program — all constraints bind.) -/

/- A good move: Open→Settling (status 0→1), `seq` ticks up (3→4), conservation held (escrowed 100,
paidOut 0 → escrowed 70, paidOut 30; 70+30 = 100). ADMITTED. -/
#eval ledgerSM.admits 0
  (.record [("escrowed", .int 100), ("paidOut", .int 0), ("seq", .int 3), ("status", .int 0)])
  (.record [("escrowed", .int 70),  ("paidOut", .int 30), ("seq", .int 4), ("status", .int 1)])  -- true

example : ledgerSM.admits 0
  (.record [("escrowed", .int 100), ("paidOut", .int 0), ("seq", .int 3), ("status", .int 0)])
  (.record [("escrowed", .int 70),  ("paidOut", .int 30), ("seq", .int 4), ("status", .int 1)]) = true := by decide

/- A bad move — conservation VIOLATED (70 + 40 = 110 ≠ 100). REJECTED (fail-closed). -/
#eval ledgerSM.admits 0
  (.record [("escrowed", .int 100), ("paidOut", .int 0), ("seq", .int 3), ("status", .int 0)])
  (.record [("escrowed", .int 70),  ("paidOut", .int 40), ("seq", .int 4), ("status", .int 1)])  -- false

example : ledgerSM.admits 0
  (.record [("escrowed", .int 100), ("paidOut", .int 0), ("seq", .int 3), ("status", .int 0)])
  (.record [("escrowed", .int 70),  ("paidOut", .int 40), ("seq", .int 4), ("status", .int 1)]) = false := by decide

/- A bad move — `seq` DECREASED (3 → 2), monotone violated. REJECTED. -/
#eval ledgerSM.admits 0
  (.record [("escrowed", .int 100), ("paidOut", .int 0), ("seq", .int 3), ("status", .int 0)])
  (.record [("escrowed", .int 70),  ("paidOut", .int 30), ("seq", .int 2), ("status", .int 1)])  -- false

example : ledgerSM.admits 0
  (.record [("escrowed", .int 100), ("paidOut", .int 0), ("seq", .int 3), ("status", .int 0)])
  (.record [("escrowed", .int 70),  ("paidOut", .int 30), ("seq", .int 2), ("status", .int 1)]) = false := by decide

/- A bad move — illegal lifecycle edge Open→Settled (status 0→2, not an allowed edge). REJECTED. -/
#eval ledgerSM.admits 0
  (.record [("escrowed", .int 100), ("paidOut", .int 0), ("seq", .int 3), ("status", .int 0)])
  (.record [("escrowed", .int 70),  ("paidOut", .int 30), ("seq", .int 4), ("status", .int 2)])  -- false

example : ledgerSM.admits 0
  (.record [("escrowed", .int 100), ("paidOut", .int 0), ("seq", .int 3), ("status", .int 0)])
  (.record [("escrowed", .int 70),  ("paidOut", .int 30), ("seq", .int 4), ("status", .int 2)]) = false := by decide

end Dregg2.Proof.WPCatalog
