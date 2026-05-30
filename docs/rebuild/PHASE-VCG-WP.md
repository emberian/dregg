> **Provenance.** Recovered 2026-05-30 from the prior session's read-only study agent
> (`~/.claude/.../subagents/`), which designed this as the body for this path but could not
> write it (read-only `Plan` mode). Verbatim except for stripped read-only-mode preamble.
> Consolidated alongside `PHASE-SHIFT.md`.

# PHASE-VCG-WP — verifying dregg *programs*: a VCG + WP calculus over the dregg kernel

> **Scope.** A design study (research + recommendation, NOT a build). "How do we verify
> dregg programs — cells/turns/applications — the way l4v/AutoCorres verifies C against the
> seL4 spec?" Reads the executable kernel (`Dregg2/Exec/Kernel.lean`, `Exec/StepComplete.lean`,
> `Exec/RecordCellLive.lean`), the run-invariant lift (`Execution.lean`, `Boundary.lean`),
> the resource camera (`Resource.lean`/`StepCamera.lean`), and the spec (`Spec/Conservation.lean`),
> against the program-logic / separation-logic / l4v literature in `pdfs/`. Tags: `[C]`
> grounded-in-code (`file:line`) · `[G]` grounded-in-paper · `[F]` forward-design · `[!]` hard limit.

---

## 0. The question, and what already exists

dregg's metatheory today proves **conservation/authority hold along an arbitrary run** — but it
proves them *per fixed program*, by hand, one `theorem` per cell. There is no *calculus* that
takes an arbitrary `RecordProgram` + a developer-supplied pre/post/invariant and **generates the
proof obligations**. That calculus is the l4v/AutoCorres analog: AutoCorres lifts seL4's C into a
monadic shallow embedding and gives a **weakest-precondition VCG** (`wp` + `wpc`) that discharges
Hoare triples about kernel functions semi-automatically. dregg wants the same machine over `recExec`/
`exec`/`cexec`. `[G: l4v/AutoCorres; sel4-information-flow-enforcement]`

**What is already built (the soundness substrate the WP must rest on):**

- `Exec.exec : KernelState → Turn → Option KernelState` — the fail-closed transition; `exec_conserves`,
  `exec_authorized`, `exec_unauthorized_fails` PROVED. `[C: Exec/Kernel.lean:69, 109, 125, 134]`
- `Exec.cexec` over `ChainedState` (kernel + receipt log) with **`cexec_attests`** — every committed
  step attests the full `fullStepInv = consP ∧ authP ∧ chainP ∧ obsP`. `[C: Exec/StepComplete.lean:39, 74]`
- `Execution.invariant_run` — the keystone induction: a `StepInvariant` lifts to every reachable config.
  `[C: Execution.lean:65]`
- `Boundary.stepComplete_preserves` — the abstract "no drifting future" safety keystone, proved *via*
  `invariant_run`: step-completeness + a `Good`-preservation lemma ⇒ `Good` holds along the whole run.
  `[C: Boundary.lean:177]`
- `RecordCell.recReplay_preserves_sumEquals` and `recordCell_run_preserves_sumEquals` — the *headline*
  worked instance: a `sumEquals`-program conserves Σ over every successful replay, re-derived through
  `stepComplete_preserves`. `[C: Exec/RecordCellLive.lean:169, 228]`
- `Resource.lean`/`StepCamera.lean` — the Iris-camera tier (discrete RA: `ℕ`/`Excl`/`Auth`; the
  frame-preserving update `Fpu` as the substructural conservation law) and the step-indexed promotion.
  `[C: Resource.lean:103, 296; StepCamera.lean]`

**The gap.** Every one of those proofs is a *bespoke* `theorem` written by a human who already knew
the invariant. There is no `vcg`/`wp` function that, given `(program, pre, post)`, *computes* the
obligations and feeds them to `dregg_auto` / domain tactics. This document recommends that machine and
its soundness obligation.

---

## 1. The program logic — recommended shape

### 1.1 The decision: a **WP / characteristic-formula** calculus, not raw Hoare triples

Three candidate shapes, scored against the existing substrate:

| Shape | Fit to dregg | Verdict |
|---|---|---|
| Hoare triples `{P} t {Q}` as a primitive `Prop` + manual rule application | works, but the user must *find* the proof tree | secondary surface |
| **`wp t Q` as a computed predicate** (`wp` pushed backward through the program structure) | matches AutoCorres exactly; the `Option`-monad shape of `recExec`/`cexec` *is* a partial-correctness monad; `dregg_auto` discharges the residue | **PRIMARY** |
| Characteristic formulae (CFML-style: a per-program formula `⟦t⟧` whose validity ≡ correctness) | the cleanest for *whole-cell-over-time*; but heavier to bootstrap | the `νF` lift, phase 2 |

**Recommendation:** build the **WP calculus** as the engine; expose **Hoare triples as the user-facing
spec surface** defined *in terms of* `wp` (`Triple P t Q := ∀ s, P s → wp t Q s`); reserve
**characteristic formulae** for the unbounded-life (`νF`) statement in §5. This is exactly l4v's layering:
triples are the surface, `wp` is the workhorse, the validity definition is the soundness anchor.
`[G: AutoCorres; characteristic-formulae/CFML]` `[F]`

### 1.2 The triple over a single turn

dregg has three transition granularities; the WP is defined at each, all three sharing one validity def:

-- partial-correctness validity (fail-closed turns are vacuously safe — the `none` branch)
def wp (step : σ → α → Option σ) (t : α) (Q : σ → Prop) (s : σ) : Prop :=
  ∀ s', step s t = some s' → Q s'

def Triple (step) (P : σ → Prop) (t) (Q : σ → Prop) : Prop :=
  ∀ s, P s → wp step t Q s

Instantiated at the three layers already in the tree:
- **record turn:** `step = recCexec`, `σ = RecChained`, `α = RecOp` — `wp recCexec`. `[C: RecordCellLive.lean:60]`
- **ledger turn:** `step = cexec`, `σ = ChainedState`, `α = Turn` — `wp cexec`. `[C: StepComplete.lean:39]`
- **bare kernel:** `step = exec`, `σ = KernelState` — `wp exec`. `[C: Kernel.lean:69]`

The `Option` is the partiality of the coalgebra arrow (`RecordCell.lean` docstring: "the `Option` IS
the partiality"). Partial correctness is the right default: a *rejected* (fail-closed) turn trivially
satisfies any post-condition — dregg's safety is "nothing bad commits", not "every turn commits".
A separate *progress/admissibility* obligation (the `Final`/`Progresses` shape of `Execution.lean:84-90`)
captures "this turn *does* commit" when the developer wants liveness. `[F]`

### 1.3 The separation-logic / camera treatment of conservation (the substructural heart)

Conservation is **substructural**: a resource cannot be copied or discarded (`Spec/Conservation.lean`'s
`Conservative` color requires a paired sibling; `Resource.Excl.excl_no_dup` proves non-duplication).
A purely predicate-transformer WP over a *global* `KernelState` does **not** express "this turn touches
only cells `{src, dst}` and frames the rest." That framing is exactly separation logic's `*` and the
camera's **frame-preserving update**. `[C: Resource.lean:185, 296]` `[G: iris-from-the-ground-up; concurrent-separation-logic-brookes-ohearn]`

**Recommended treatment — two registers, matching the existing two-mode camera note:**

1. **Ownership assertions over the camera.** A heap-style assertion language over `Auth M`
   (`Resource.lean:209`): `own(cell, ◦f)` = "this turn holds fragment `f` of `cell`", with the
   separating conjunction `P * Q` meaning *disjoint* fragments compose validly (`Auth.op` is `invalid`
   when two authoritatives collide; fragments add). The **frame rule** is then
   `{P} t {Q}  ⟹  {P * R} t {Q * R}` whenever `t`'s footprint is disjoint from `R` — and its
   soundness is *literally* `Fpu` (`Resource.lean:103`): replacing the turn's pre-resource by its
   post-resource preserves every frame `R` a third party holds. `conservation_is_fpu`
   (`Resource.lean:296`) is the frame rule's semantic core, already PROVED.

2. **The conservation triple as an FPU obligation.** A `Conservative`-colored turn's WP obligation is
   `ConservesResource pre post := Fpu pre post` (`Resource.lean:110`). For the cleartext ledger this
   collapses to the `Σ`-preservation already proved (`fpu_of_total` for `ℕ`; `transfer_sum_conserve`
   for the `Finset` ledger). For the **private** case the *same* triple runs over the commitment group
   (`Spec/Conservation.committed_iff_cleartext`, `Conservation.lean:337`) — the separation assertion is
   monoid-generic, so "hidden yet provably conserved" is one instantiation, not a new logic.

**Why this is the right substructural flavor and not overkill:** dregg's intra-vat runtime is the
*validity oracle* (`Resource.lean` two-mode note) — so the **discrete** RA + the frame rule is the
canonical tier. The full step-indexed Iris `iProp` (with `▷`-guarded recursive invariants) is needed
**only** when a cap's validity quantifies over *another cell's* invariant (`StepCamera.lean`'s motivating
case). The first WP does **not** need it — see §5. `[C: Resource.lean:32-55; StepCamera.lean:8-37]` `[F]`

### 1.4 How `invariant_run`/`stepComplete_preserves` becomes WP-soundness

The bridge is exact and *already proved at the run level*: a Hoare triple about a **whole cell life** is
an instance of `stepComplete_preserves`. Concretely, the WP-over-a-run soundness theorem is:

-- if every committed step satisfies `wp step t I` (i.e. preserves the invariant I),
-- then I holds at every reachable configuration of the cell's whole run.
RunTriple P I  :=  (∀ s, I s → ∀ t s', step s t = some s' → I s')   -- the StepInvariant
                   → ∀ s s', Run (system step) s s' → I s → I s'

This is `Execution.invariant_run` (`Execution.lean:65`) verbatim, with the hypothesis being precisely
`StepInvariant`, which is `wp` quantified over all turns: `StepInvariant ≡ ∀ t, Triple I t I`. So:

> **The existing safety lift IS the soundness of the run-level WP.** `invariant_run` /
> `stepComplete_preserves` say: *a per-turn WP-discharged invariant lifts to the whole execution.*
> The VCG only needs to **generate** the per-turn `Triple I t I` obligations; `invariant_run` already
> closes the lift, axiom-clean. `[C: Execution.lean:65; Boundary.lean:177; StepComplete.lean:106]`

---

## 2. The VCG — the pipeline `program + spec → VCs → tactics → proof`

### 2.1 What the VCG consumes

A **cell verification problem** = `(program : RecordProgram, spec : CellSpec)` where:

structure CellSpec where
  pre  : Value → Prop          -- precondition on the initial record
  post : Value → Prop          -- postcondition (per committed turn, or at a final/observed state)
  inv  : Value → Prop          -- the cell invariant (what holds at every reachable state)

The developer authors `inv` (e.g. `Σ{a,b} = 10`, or `count` monotone, or `status ∈ {0,1,2}`); the VCG
generates what must be discharged for `inv` to be a genuine run-invariant of `program`.

### 2.2 WP pushed through the `RecordProgram` structure (the generator)

The key observation: **`RecordProgram.admits` already *is* a syntactic predicate** — a decidable Boolean
over named fields (`Program.lean:216`). So `wp recCexec op Q s` *computes symbolically* by case-splitting
the program structure. The VCG is the function that performs that push:

vcg : RecordProgram → CellSpec → List VC

generating, for each program constructor, these obligation classes (each a closed `Prop` goal):

1. **Admissibility → invariant preservation (the core VC).**
   For every op `op` and every state `s` with `inv s.value`:
   `program.admits method s.value (applyOp s.value op) = true → inv (applyOp s.value op)`.
   I.e. *"whenever the program's gate fires, the post-state still satisfies `inv`."* This is the WP of
   `recCexec` unfolded through `recCexec_attests` (`RecordCellLive.lean:87`): a commit's post-value is
   exactly `applyOp s.value op` and was `admits`-true. For a `.predicate cs` program this VC is generated
   *per constraint*, and `admits_sumEquals` (`RecordCellLive.lean:131`) is the already-proved discharge
   template — the VC for a `sumEquals` constraint closes by `admits_sumEquals` + `eq_of_beq`.

2. **Stay-put preservation (fail-closed branch — trivial VC).**
   `inv s.value → inv s.value` (the rejected-turn self-loop, `recNext_commits_or_stays`,
   `RecordCellLive.lean:115`). Auto-closed by `id`.

3. **Initialization VC.** `pre s.value → inv s.value` (the invariant holds at start).

4. **Postcondition VC.** `inv s.value → post s.value` (or, for observed posts, `inv → post` at the
   `Obs` projection). Often `post = inv`.

5. **Conservation VC (camera obligation, for `Conservative`-colored ops).**
   `Fpu pre post` over the cell's resource (`Resource.lean:110`) — discharged by `conservation_is_fpu`
   (`Resource.lean:296`) or, for the ledger, `transfer_sum_conserve` (`Kernel.lean:90`).

6. **Cross-cell binding VC (deferred / hypothesis).** For `boundDelta` constraints the single-cell
   evaluator returns `true` (`Program.lean:151`); the VC is *declared* and routed to the JointTurn
   aggregate as an explicit **hypothesis** (CG-2 ⊗ CG-5), never derived — honoring the inviolable rule
   (`ROADMAP.md`, `JointCell.lean` docstring). `[C: Exec/JointCell.lean]`

### 2.3 The tactic side (the metaprogramming study — discharge)

The generated VCs are *exactly* the shape `dregg_auto` and a small domain tactic family already close:

- VC class 1 for arithmetic constraints (`sumEquals`, `monotonic`, `fieldDelta`, `allowedTransitions`):
  `simp [RecordProgram.admits, evalConstraint, ...]` to expose the Boolean, then `omega`/`decide`/
  `eq_of_beq` — the exact moves in `recExec_mono_holds` (`RecordCell.lean:160`) and `admits_sumEquals`.
- VC class 2/3/4: `dregg_auto` (`Tactics.lean:52`) closes reflexive/`simp_all`/`omega` residue.
- A new **`vcg_discharge` macro** = `(intro · ; simp only [admits, evalConstraint, applyOp]; first | dregg_auto | <domain solver>)`,
  one per constraint family. This is the metaprogramming deliverable: a tactic that turns the *structural*
  VC into a *closed* proof, with `#assert_axioms` (`Tactics.lean:38`) pinning each result kernel-clean.

**Pipeline end-to-end:** `(program, spec) → vcg → List VC → vcg_discharge* → all closed → RunTriple`
(via `invariant_run`). The capstone theorem the VCG produces is `inv` holds along every run — the
machine-generated analog of the hand-written `recordCell_run_preserves_sumEquals`. `[C: RecordCellLive.lean:228]` `[F]`

---

## 3. Soundness — the `wp`-soundness theorem shape

The VCG/WP is sound iff a closed VC set entails a true statement about the **operational** `exec`/`cexec`/
`recCexec`. Two theorems, both *reducing to already-proved keystones*:

### 3.1 Per-step soundness (the `wp` is faithful to `recCexec`)

theorem wp_sound (s : RecChained) (op : RecOp) (Q : Value → Prop)
    (h : wp recCexec op (fun s' => Q s'.value) s) :
  ∀ s', recCexec s op = some s' → Q s'.value

This is *definitional* (`wp` unfolds to exactly this), but the **content** is that `recCexec`'s commit
implies the `StepInv` facts — i.e. it factors through `recCexec_attests` (`RecordCellLive.lean:87`).
So per-step WP-soundness is `recCexec_attests` re-packaged: the WP only ever asserts properties of the
*genuinely-gated* post-state. The ledger analog factors through `cexec_attests` (`StepComplete.lean:74`).

### 3.2 Run soundness (the VCG's capstone is faithful to the whole execution)

theorem vcg_run_sound (program) (spec)
    (hVCs : all_discharged (vcg program spec))   -- every generated VC closed
    {s s'} (hrun : Run (recordSystem program) s s') (h0 : spec.pre s.value) :
  spec.inv s'.value ∧ (spec.post s'.value)

**Proof shape:** the discharged VC class 1+2 give `StepInvariant (fun c => inv c.value)`; VC class 3
gives `inv s.value` from `pre`; then **`stepComplete_preserves`** (`Boundary.lean:177`) /
**`invariant_run`** (`Execution.lean:65`) lift `inv` to `s'`; VC class 4 turns `inv s'` into `post s'`.
This is *structurally identical* to the proof of `recordCell_run_preserves_sumEquals`
(`RecordCellLive.lean:228-247`) — the VCG just generates the `hpres` lemma the human wrote by hand.

> **The single soundness obligation of the whole machine:** *prove `vcg_run_sound` once* — that a fully
> discharged VC set instantiates `stepComplete_preserves`'s `hpres` hypothesis. Everything else (the
> per-constraint VC closers) is per-program automation that `#assert_axioms` keeps honest. `[C: Boundary.lean:177; RecordCellLive.lean:228]` `[F]`

### 3.3 Tie to `cexec_attests` / `stepComplete_preserves` — explicitly

- `cexec_attests` ⟹ per-step WP-soundness for the ledger turn (the `consP`/`authP`/`chainP`/`obsP`
  conjuncts ARE the four atomic post-conditions the WP can assert). `[C: StepComplete.lean:74]`
- `stepComplete_preserves` ⟹ run-level WP-soundness (the lift). The VCG never re-proves the lift; it
  *feeds* it. `[C: Boundary.lean:177]`
- The conservation-as-FPU triple's frame-rule soundness is `conservation_is_fpu`. `[C: Resource.lean:296]`

---

## 4. A worked example — the monotonic counter (and the escrow sketch)

### 4.1 Monotonic counter (fully closable on today's substrate)

**Program** (already in-tree): `monoCountProgram := .predicate [.simple (.monotonic "count")]`
(`RecordCell.lean:158`).
**Spec:** `pre := (count present)`, `inv := λ v, ∃ n, v.scalar "count" = some n` and the *relational*
invariant "count never decreases", `post := inv`.

**The triple:** `{ count = n₀ }  op  { count ≥ n₀ }`, for every `op`, lifted to the run:
`Run ⟹ count(s') ≥ count(s)`.

**VCs the generator emits:**
1. *Admissibility→preservation:* `monoCountProgram.admits 0 old new = true → new.scalar "count" ≥ old.scalar "count"`.
   **Closes by** `recExec_mono_holds` (`RecordCell.lean:160`) — already PROVED: `simp` the `admits`
   down to the `monotonic` Boolean, then `intLe`/`omega`.
2. *Stay-put:* trivial (`recNext_commits_or_stays`, `RecordCellLive.lean:115`).
3. *Init/Post:* reflexive.

**How it closes the run:** instantiate `stepComplete_preserves` with `Good := λ s, count s.value ≥ n₀`,
`hpres` discharged by VC 1 on commit and `hstay` on stay-put — verbatim the `recordCell_run_preserves_sumEquals`
template (`RecordCellLive.lean:236`). The `#eval` witnesses are already in the file (increment commits and
ticks the chain; decrement rejected, stays put — `RecordCellLive.lean:266-269`). **This example is
buildable today with no new metatheory — it is the VCG retracing an existing hand proof.** `[C]`

### 4.2 Escrow (the two-state-machine + conservation example — the realistic stretch)

**Program:** a `.cases` program over `status ∈ {Open=0, Claimed=1, Paid=2}` with a `Conservative`
`escrowed` balance:
.cases [ ⟨.methodIs claim, [.allowedTransitions "status" [(0,1)]]⟩,
         ⟨.methodIs pay,   [.allowedTransitions "status" [(1,2)],
                            .sumEqualsAcross ["escrowed"] ["paidOut"]]⟩ ]
(`allowedTransitions`/`sumEqualsAcross` both exist: `Program.lean:91, 95`; `.cases` default-deny is the
fail-closed arrow, `Program.lean:219`.)

**Spec:** `inv := (status ∈ {0,1,2}) ∧ (escrowed + paidOut = deposit₀)` — a **state-machine safety**
invariant ∧ a **conservation** invariant.

**VCs the generator emits:**
1. *Per-arm admissibility→preservation:* the `claim` arm preserves `status ∈ {0,1,2}` (closes by
   `allowedTransitions` `decide`); the `pay` arm preserves *both* the SM bound and `sumEqualsAcross`
   (closes by `admits` → `evalConstraint .sumEqualsAcross` → `eq_of_beq`, the `splitProgram` template,
   `Program.lean:287`).
2. *Default-deny:* any unmatched method ⇒ `admits = false` ⇒ stay-put ⇒ `inv` trivially preserved
   (`admits_cases_nil`, `Program.lean:235`).
3. *Conservation VC (camera):* the `escrowed` move is `Conservative` (`Spec/Conservation.lean:165`);
   its FPU obligation closes by `conservation_is_fpu` over `Auth ℤ`, or — if the escrow is single-ledger —
   by the `sumEqualsAcross` arithmetic directly. **Cross-cell** escrow (payer in vat A, payee in vat B)
   routes conservation to the JointTurn CG-5 binding as a hypothesis (`JointCell.joint_cg5_conserves`),
   *not* derived from the two per-cell triples. `[!: the inviolable rule]`

**Status:** arms 1–2 are closable today (the constraint evaluators + their `admits_*` lemmas exist).
Arm 3's *single-ledger* case is closable; the *cross-vat* case needs the JointTurn binding wired as a
WP side-condition — a clean phase-2 extension, not a soundness hole. `[F]`

---

## 5. Scope honesty — tractable-now vs Iris-step-indexed

### 5.1 Tractable NOW (the realistic first version)

- **A WP over the `Option`-monad transition** (`recCexec`/`cexec`/`exec`) with `Triple` defined via `wp`.
  The substrate (`recCexec_attests`, `cexec_attests`) makes per-step soundness *definitional*.
- **A VCG over `RecordProgram`** generating VC classes 1–4 by symbolic push through `admits` (a decidable
  Boolean — the generation is computable). The constraint catalog is finite and already has per-constraint
  `admits_*` discharge lemmas (`admits_sumEquals`, `recExec_mono_holds`).
- **Run-level soundness for free** via `invariant_run`/`stepComplete_preserves` — the lift is *already
  proved, axiom-clean*. The VCG only generates the `hpres` lemma.
- **Conservation as a *discrete*-camera frame rule** (`Fpu` over `ℕ`/`ℤ`/`Auth M`); `conservation_is_fpu`
  is proved. The cleartext↔commitment equivalence (`committed_iff_cleartext`) makes the private case the
  same triple over a different monoid.
- **The two worked examples (counter fully; escrow single-ledger)** — both retrace existing hand proofs,
  which is the correctness check on the generator.

This first version is **a safety-invariant WP over the toy/record kernel** — exactly the AutoCorres
analog at dregg's current maturity: a VCG that mechanizes the per-program invariant proofs that are today
written by hand. `[F]`

### 5.2 Needs the Iris step-indexed machinery (DEFER)

- **Higher-order / recursive resource invariants** — a cap whose validity asserts *another cell maintains
  an invariant `Q`* (`StepCamera.lean:8-37`). This is the negative self-reference `R ≅ (R → Prop)` that
  forces the step-indexed OFE + guarded fixpoint; the discrete-RA frame rule cannot host it. `[!]`
- **Coinductive/`νF` characteristic formulae for unbounded cell life** — stating "the cell is forever
  correct" as a `▶`-guarded CF rather than a run-invariant. `Boundary.Later` and `StepCamera.Later` are
  the SAME `▷`; the CF would live under it. Tractable as a *second* phase once the run-invariant WP exists,
  because `recordCell` is already a genuine `TurnCoalg` (`RecordCellLive.lean:76`).
- **Concurrent/cross-vat separation** with shared invariants (the `iProp`-over-camera build). Needed only
  when cells reason about each other's *futures*; the single-cell WP and the JointTurn-hypothesis escrow
  do not. `[C: StepCamera.lean:178; Resource.lean:53]`

The honest line: **the first WP is partial-correctness, single-cell, discrete-camera, run-invariant** —
and it is *fully supported by today's proved keystones*. The step-indexed `iProp` is a real, separate
research increment, correctly fenced off in `StepCamera.lean` already.

---

## 6. Recommended minimal VCG/WP to build first + its soundness obligation

**Build first (minimal, all on today's substrate):**

1. `wp (step : σ → α → Option σ) (t) (Q : σ → Prop) (s) := ∀ s', step s t = some s' → Q s'`, and
   `Triple step P t Q := ∀ s, P s → wp step t Q s`. Instantiate at `recCexec`.  `[C: RecordCellLive.lean:60]`
2. `vcg : RecordProgram → CellSpec → List Prop` — VC classes 1 (admissibility→`inv`-preservation,
   per constraint), 2 (stay-put), 3 (init), 4 (post). Symbolic push through `RecordProgram.admits`.
   `[C: Program.lean:216]`
3. A `vcg_discharge` tactic family (one closer per constraint kind) reusing `recExec_mono_holds` /
   `admits_sumEquals` / `dregg_auto`, each pinned by `#assert_axioms`.  `[C: RecordCell.lean:160; RecordCellLive.lean:131; Tactics.lean:38]`
4. The two worked examples (§4) as the regression check — generator output must match the hand proofs.

**The single soundness obligation to discharge:**

> **`vcg_run_sound`** — *a fully discharged VC set entails `inv` holds along every `Run` of the record
> cell.* Proof: the VCs give `StepInvariant (λ c, inv c.value)`; conclude by **`stepComplete_preserves`**
> (`Boundary.lean:177`) / **`invariant_run`** (`Execution.lean:65`). This is the *generated* form of
> `recordCell_run_preserves_sumEquals` (`RecordCellLive.lean:228`); proving it once makes every
> VCG-discharged cell sound w.r.t. the operational `recCexec`. Keep it `#assert_axioms`-clean.

Per-step soundness is `recCexec_attests`/`cexec_attests` re-packaged and needs no new proof. The camera
frame rule's soundness is `conservation_is_fpu`. **No new axioms, no `sorry` — the VCG is a generator over
proved keystones.** `[C: RecordCellLive.lean:87; StepComplete.lean:74; Resource.lean:296]`

---

## Literature anchors (cited)

- **AutoCorres / l4v / seL4** — the C-refinement + `wp`/`wpc` VCG this phase is the analog of; the
  monadic shallow embedding + Hoare-triple surface. (`pdfs/sel4-information-flow-enforcement.pdf`;
  l4v/AutoCorres read from `~/dev/l4v`.) `[G]`
- **Iris** (`iris-from-the-ground-up.pdf`, `beginners-guide-iris-coq-separation-logic-2105.12077.pdf`) —
  the camera, frame-preserving update, `▷`-guarded recursive ghost state; the substructural conservation
  treatment and the step-indexed tier. `[G]`
- **Concurrent separation logic** (`concurrent-separation-logic-brookes-ohearn.pdf`) — the frame rule and
  `*`, the basis for "this turn touches only its footprint." `[G]`
- **DISEL** (`disel-distributed-separation-logic.pdf`), **Igloo** (`igloo-refinement-separation-logic-oopsla20.pdf`) —
  distributed/refinement separation logic = the cross-vat extension template (the spec↔impl bridge). `[G]`
- **Mathematical theory of resources** (`mathematical-theory-of-resources.pdf`) — conservation as
  symmetric-monoidal; the `Conservative`-color law's categorical home. `[G]`
- Characteristic-formulae / CFML (Charguéraud) — the `νF`-life CF in §5.2. `[G, external]`

---

*Companion to: `Exec/Kernel.lean`, `Exec/StepComplete.lean`, `Exec/RecordCellLive.lean`,
`Execution.lean`, `Boundary.lean`, `Resource.lean`, `StepCamera.lean`, `Spec/Conservation.lean`,
`Exec/Program.lean`. Read after `ROADMAP.md` Phase 0–2 (step-completeness) and `study-category.md`.*

---
