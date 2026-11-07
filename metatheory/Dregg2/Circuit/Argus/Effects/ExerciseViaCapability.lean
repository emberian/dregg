/-
# Dregg2.Circuit.Argus.Effects.ExerciseViaCapability — dregg1's `Effect::ExerciseViaCapability`
  (act THROUGH a held cap) welded into the Argus IR, on its HONEST hold-gate surface.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn/createEscrow; the sibling welds carried per-component effects (`BalanceA`/
`CellSeal` to their genuine standalone v2 `Surface2` descriptors, `DropRef` to the per-cell cap-root
descriptor). This module welds **`exerciseViaCapability`** — dregg1's `Effect::ExerciseViaCapability {
cap_slot→target, inner_effects }` (`apply.rs:2441`), the act-through-a-held-cap effect — in its own
disjoint file. It OWNS only itself, imports the Argus IR + the audited `exerciseA` EffectVM emit module
read-only, and edits no other Argus file.

## What ExerciseViaCapability IS — and the layer this weld pins (read this; the surface is precise)

dregg1's exercise is a **hold-gate → facet-mask → RECURSE** composite (`Handlers/Exercise.lean §0`):

  1. (hold-gate) the actor must HOLD a cap conferring an edge to `target` (`confersEdgeTo`); the cap
     graph is UNCHANGED by exercising (it READS, never edits, the c-list — `apply.rs:2455`);
  2. (R4 facet-mask) each inner effect must be ADMITTED under the held cap's `allowed_effects`;
  3. (recurse) each surviving inner effect is APPLIED in sequence against the target — a SUB-FOREST.

The verified executor splits this into an OUTER hold-gate step `exerciseStepA` (`TurnExecutorFull.lean:
1601`) and the inner fold `execInnerA`, glued by the runnable arm
`execFullA s (.exerciseA actor t inner) = if innerFacetsAdmittedA … then (match exerciseStepA … with
some s' => execInnerA s' inner | none => none) else none` (`TurnExecutorFull.lean:3811`).

This weld pins the **OUTER HOLD-GATE LAYER** — the bare cap-exercise (`inner = []`). That is the exact
layer the AUDITED descriptor connector speaks about: `EffectVmEmitExercise.descriptor_agrees_with_executor
_exercise` welds the runnable `exerciseVmDescriptor` against `ExerciseHoldSpec`/`exerciseStepA`, NOT the
inner fold (each inner effect is its OWN per-row descriptor, composed at the turn layer `TurnEmit` —
`EffectVmEmitExercise §0`, `Handlers/Exercise §DEFER`, cited). So the honest object here is the hold-gate
outer step; the inner forest is the turn-composition layer, OUT of this per-effect weld (stated, §DEFER).

## The KERNEL-vs-CHAINED boundary (the structural shape, named precisely)

The Argus `interp` is a `RecordKernelState → Option RecordKernelState` transformer; `exerciseStepA` is a
`RecChainedState → Option RecChainedState` step whose ONLY state motion is (i) a hold-gate, then (ii) a
prepend of `authReceipt actor` onto the `log` — and the `log` lives in `RecChainedState`, NOT in
`RecordKernelState`. The KERNEL is FROZEN. So on the kernel, the exercise hold-gate is a PURE
DOMAIN-RESTRICTOR: gate on the hold-edge, return the kernel UNCHANGED. That is EXACTLY the `RecStmt.guard`
primitive (`Stmt.lean §guard`) — the in-band shape of the `confersEdgeTo` hold-gate, freezing the kernel.
The runtime receipt-log prepend (which the `RecordKernelState`-level `interp` structurally cannot emit) is
re-attached at the CHAINED lift (§3), exactly as `Effects/CellSeal §3` re-attaches its lifecycle receipt.
No new IR constructor is needed (the `guard` primitive is the whole kernel content).

## What this module proves (the two keystones, on the hold-gate surface)

  1. `interp_exerciseStmt_eq_kernel` — the executor IS the term: `interp` of the exercise IR term is, on
     the nose, the KERNEL projection of the verified outer step `exerciseStepA` — `if hold-gate then
     some k else none` (the kernel frozen). The per-effect executor-refinement for the cap-exercise layer.
  2. `exercise_compile_sound` — the weld: a satisfying witness of the AUDITED runnable descriptor
     `exerciseVmDescriptor` (`EffectVmEmitExercise §8`, `exerciseDescriptor_full_sound`) agrees, PER CELL,
     with the FROZEN balance the IR term's executor produces (`descriptor_agrees_with_executor_exercise`),
     carrying the per-cell `ExerciseCellSpec` (whole economic block frozen) AND the explicit NONCE-TICK
     divergence as a conjunct.

## SURFACE + THE REPORTED DIVERGENCES (precise — do NOT over-read)

  * **PER-CELL.** `exerciseVmDescriptor` is a SINGLE-ROW AIR; its soundness pins ONE cell's transition
    (frozen economic block + nonce tick) + that cell's commitment binding. `interp`/`exerciseStepA` is the
    whole-state transformer (here the IDENTITY on the kernel). We weld on the cell's projected FROZEN
    `balLo`, exactly the surface `descriptor_agrees_with_executor_exercise` supports — NOT a full-state
    `Surface2` weld (the exercise hold-layer has no standalone `Surface2`/`EffectCommit2 *_full_sound`;
    its genuine content is connectivity/non-amplification — the AUTHORITY regime `EffectsAuthority §5`,
    `exercise_non_amplifying` — and the conserved frozen frame, not a value/side-table move). The cell
    economic block is FROZEN (exercise moves no value AT THE HOLD LAYER), so the conserved leg is the
    frozen `balLo` directly.

  * **THE NONCE-TICK DIVERGENCE (kernel-freeze vs runtime row-tick — carried).** The executor
    hold-step `exerciseStepA` FREEZES the whole kernel (the cell record, nonce included). The runtime
    EffectVM row TICKS the cell nonce by 1 on this non-NoOp row (`EffectVmEmitExercise §0`, the Stage-3
    passthrough batch's global nonce gate). So the descriptor's `post.nonce = pre.nonce + 1` while the
    executor's projected post-nonce is FROZEN (`= pre.nonce`). This is the SAME structural divergence
    transfer/burn carry (row ticks, body freezes), and on the cap-exercise layer it is left as an EXPLICIT
    conjunct of the weld (`post.nonce = pre.nonce + 1`), reconciled at the turn level by the prologue's
    single tick (`Argus.Nonce.perEffect_nonce_reconciles_to_turn`, cited — not re-proved here).

  * **OUTER-LAYER-ONLY (inner fold OFF-ROW — stated §DEFER).** The weld pins the bare cap-exercise
    (`inner = []`). The inner sub-forest (R4 facet-mask + the `execInnerA` fold) is the turn-composition
    layer; its conservation is the algebra twin `Handlers.Exercise.exercise_conserves` (the summed inner
    deltas) and each inner effect's own per-row descriptor — cited, NOT claimed here.

## Axiom hygiene

`#assert_axioms` on both headline theorems ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR enters ONLY via the cited descriptor
soundness lemmas (their own named hypotheses). Imports are read-only; this file owns only itself and edits
no other Argus module.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitExercise
import Dregg2.Circuit.Emit.EffectVmEmitExerciseWide

namespace Dregg2.Circuit.Argus.Effects.ExerciseViaCapability

open Dregg2.Exec
-- `execFullA` (the runnable action executor) + `exerciseStepA` (the chained outer hold-step the
-- `exerciseA` arm routes to) + `RecChainedState` live in `TurnExecutorFull`; opened so §3's chained-arm
-- lift can name them. `execInnerA`/`innerFacetsAdmittedA` are the inner-fold helpers the arm threads.
open Dregg2.Exec.TurnExecutorFull
  (execFullA exerciseStepA execInnerA innerFacetsAdmittedA acceptsEffects authReceipt)
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Exec (RecordKernelState RecChainedState CellId confersEdgeTo)
open Dregg2.Authority (Cap)
-- The audited runnable descriptor + its per-cell soundness/connector (the circuit side of the weld).
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitExercise
  (exerciseVmDescriptor RowEncodesExercise ExerciseCellSpec exerciseDescriptor_full_sound
   descriptor_agrees_with_executor_exercise balProj)
-- The universe-A hold-gate spec the connector consumes (kernel-freeze + receipt prepend).
open Dregg2.Circuit.ActionDispatch (ExerciseHoldSpec exerciseHoldState exerciseStepA_iff_holdSpec)

set_option autoImplicit false

/-! ## §1 — The exercise effect as an Argus IR term (the hold-gate; a pure `guard`, kernel frozen).

`exerciseStepA s actor target = if (s.kernel.caps actor).any (confersEdgeTo target ·) then some { s with
log := authReceipt actor :: s.log } else none` — the kernel is FROZEN; the only state motion is the
log prepend (a `RecChainedState` field). So the KERNEL content of the cap-exercise is EXACTLY a
domain-restrictor on the hold-edge: gate, then leave the kernel verbatim. The `RecStmt.guard` primitive
(`Stmt.lean §guard`) is that shape — no new IR constructor. -/

/-- The exercise hold-gate as a `Bool` predicate over the KERNEL — exactly `exerciseStepA`'s `if`: the
actor holds SOME cap conferring an edge to `target` (`confersEdgeTo`). This is the EXACT executor
hold-gate (NOT the R4 facet-mask, which gates the inner fold — out of this outer-layer weld, §DEFER). -/
def exerciseGuardB (actor target : CellId) (k : RecordKernelState) : Bool :=
  (k.caps actor).any (fun cap => confersEdgeTo target cap)

/-- **The exercise effect as an IR term: the hold-gate, kernel frozen.** A single `RecStmt.guard` of the
`confersEdgeTo` hold-edge predicate. Unlike transfer/balanceA (gate THEN a `setCell`/`setBal` move) the
cap-exercise HOLD LAYER moves nothing in the kernel — it READS the c-list (`apply.rs:2455`), so the term
is a bare `guard` (a pure domain-restrictor). The runtime receipt-log prepend is re-attached at the
chained lift (§3); the inner sub-forest is the turn-composition layer (§DEFER). -/
def exerciseStmt (actor target : CellId) : RecStmt :=
  RecStmt.guard (exerciseGuardB actor target)

/-! ## §2 — THE CORNERSTONE: `interp` of the term IS the KERNEL projection of `exerciseStepA`. -/

/-- The exercise hold-gate `Bool` over the kernel decodes to `exerciseStepA`'s `if` condition (the
`confersEdgeTo` hold-edge). The analog of `transferGuard_iff`, here a single conjunct. -/
theorem exerciseGuardB_iff (actor target : CellId) (k : RecordKernelState) :
    exerciseGuardB actor target k = true ↔
      (k.caps actor).any (fun cap => confersEdgeTo target cap) = true := by
  rfl

/-- **The cornerstone (hold-gate, kernel-frozen).** `interp` of the exercise term IS the KERNEL
projection of the verified outer step `exerciseStepA`: on the same `confersEdgeTo` hold-gate, the term
commits to the kernel UNCHANGED (`some k`) and rejects (`none`) on exactly the same gate. Stated as
`(exerciseStepA s actor target).map (·.kernel)` (the executor freezes the kernel, so its kernel
projection is `if hold-gate then some s.kernel else none`), this is the per-effect executor-refinement
for the cap-exercise OUTER layer — the in-band `RecStmt.guard` shape of the `confersEdgeTo` hold-gate.
The runtime receipt-log prepend (off the kernel) is re-attached in §3. -/
theorem interp_exerciseStmt_eq_kernel (s : RecChainedState) (actor target : CellId) :
    interp (exerciseStmt actor target) s.kernel
      = (exerciseStepA s actor target).map (fun st => st.kernel) := by
  -- LHS: `interp (guard φ) k = if φ k then some k else none` (the §guard clause).
  simp only [exerciseStmt, interp, exerciseGuardB]
  -- RHS: open `exerciseStepA`'s `if` on the SAME hold-gate; the committed branch freezes the kernel
  -- (`{ s with log := … }.kernel = s.kernel`), so its `.map (·.kernel)` is `some s.kernel`.
  unfold exerciseStepA
  by_cases hg : (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true
  · simp only [hg, ↓reduceIte, Option.map_some] <;> rfl
  · simp only [hg, Bool.false_eq_true, ↓reduceIte, Option.map_none]

#assert_axioms interp_exerciseStmt_eq_kernel

/-! ## §3 — Lifting the cornerstone to the CHAINED runnable arm `execFullA … (.exerciseA … [])`.

The audited descriptor connector (§4) and the `exerciseStepA_iff_holdSpec` corner speak about the CHAINED
`RecChainedState` step. The §2 cornerstone is the KERNEL projection. The chained outer layer is exactly
the §2 hold-gate PLUS the runtime receipt prepend `authReceipt actor :: s.log` (the `log` motion the
kernel `interp` cannot model). With the inner forest EMPTY (`inner = []`), the runnable `exerciseA` arm
reduces to the outer step `exerciseStepA` itself: the facet-mask gate is vacuously true (`[].all _ =
true`) and the inner fold is the identity (`execInnerA s' [] = some s'`). We bridge faithfully, naming the
receipt-row prepend EXPLICITLY in the chained post-state (the kernel-vs-runtime divergence — NOT
papered, exactly as `Effects/CellSeal §3`). -/

/-- **`execFullA_exercise_nil` — the runnable arm on the BARE cap-exercise IS the outer hold-step.** With
`inner = []`, `execFullA s (.exerciseA actor target [])` reduces to `exerciseStepA s actor target`: the
R4 facet-mask gate `innerFacetsAdmittedA s actor target []` is vacuously `true` (`[].all _`), and the
inner fold `execInnerA s' [] = some s'` is the identity, so the arm is precisely the outer hold-step. This
pins the weld to dregg1's `ExerciseViaCapability` entry point (the `exerciseA` arm), restricted to the
hold-gate layer the descriptor speaks about. -/
theorem execFullA_exercise_nil (s : RecChainedState) (actor target : CellId) :
    execFullA s (.exerciseA actor target []) = exerciseStepA s actor target := by
  -- the arm: `if innerFacetsAdmittedA … [] then (match exerciseStepA … with some s' => execInnerA s' [] …)`.
  show (if innerFacetsAdmittedA s actor target [] = true then
          match exerciseStepA s actor target with
          | some s' => execInnerA s' []
          | none    => none
        else none) = exerciseStepA s actor target
  -- the facet-mask gate is vacuously true on the empty forest …
  have hadm : innerFacetsAdmittedA s actor target [] = true := by
    simp only [innerFacetsAdmittedA, List.all_nil]
  rw [if_pos hadm]
  -- … and the inner fold `execInnerA s' []` is the identity, so the `match` collapses to `exerciseStepA`.
  cases h : exerciseStepA s actor target with
  | none => rfl
  | some s' => show execInnerA s' [] = some s'; rfl

/-- **`interp_exerciseStmt_chained` — the IR term's KERNEL executor, lifted to the runnable `exerciseA`
arm.** When the §2 cornerstone commits on the kernel (`interp (exerciseStmt actor target) s.kernel = some
k'`), the runnable action executor `execFullA s (.exerciseA actor target [])` commits to the chained state
`⟨k', authReceipt actor :: s.log⟩` (= `exerciseHoldState s actor`). So the Argus term's KERNEL meaning
lifts to the chained executor the descriptor connector speaks about, with the runtime receipt-log row
re-attached HERE (the explicit kernel-vs-runtime bridge) AND `k'` confirmed equal to the frozen kernel
`s.kernel`. -/
theorem interp_exerciseStmt_chained
    (s : RecChainedState) (actor target : CellId) (k' : RecordKernelState)
    (hexec : interp (exerciseStmt actor target) s.kernel = some k') :
    execFullA s (.exerciseA actor target []) = some { kernel := k', log := authReceipt actor :: s.log }
      ∧ k' = s.kernel := by
  -- the §2 cornerstone identifies `interp …` with the kernel projection of `exerciseStepA`.
  rw [interp_exerciseStmt_eq_kernel] at hexec
  -- so `exerciseStepA s actor target` is `some _` with kernel `k'`; factor it.
  cases hstep : exerciseStepA s actor target with
  | none => rw [hstep] at hexec; exact absurd hexec (by simp)
  | some s' =>
    rw [hstep] at hexec
    simp only [Option.map_some, Option.some.injEq] at hexec
    -- `exerciseStepA` freezes the kernel and prepends the receipt: `s' = { s with log := … }`.
    obtain ⟨_, hs'⟩ := TurnExecutorFull.exerciseStepA_factors hstep
    subst hs'
    -- `hexec : s.kernel = k'` (the frozen kernel). Substitute `k'` by the frozen kernel; both sides match.
    subst hexec
    refine ⟨?_, rfl⟩
    rw [execFullA_exercise_nil, hstep]

#assert_axioms execFullA_exercise_nil
#assert_axioms interp_exerciseStmt_chained

/-! ## §3a — the chained step as `ExerciseHoldSpec` (the connector's pre-condition, from the IR term).

`descriptor_agrees_with_executor_exercise` consumes an `ExerciseHoldSpec s actor target s'`. We derive it
from the IR-term commit, so the weld's executor hypothesis is the Argus refinement, not a bare citation. -/

/-- **`exerciseStmt_to_holdSpec` — the IR-term commit yields the connector's `ExerciseHoldSpec`.** When the
§2 cornerstone commits on the kernel, the runnable arm's chained post-state `⟨k', authReceipt actor ::
s.log⟩` satisfies `ExerciseHoldSpec s actor target ·` — the universe-A hold-gate spec (hold-edge held +
kernel frozen + receipt prepended) the descriptor connector reads. So the IR refinement SUPPLIES the
connector's pre-condition. -/
theorem exerciseStmt_to_holdSpec
    (s : RecChainedState) (actor target : CellId) (k' : RecordKernelState)
    (hexec : interp (exerciseStmt actor target) s.kernel = some k') :
    ExerciseHoldSpec s actor target { kernel := k', log := authReceipt actor :: s.log } := by
  obtain ⟨harm, _hk'⟩ := interp_exerciseStmt_chained s actor target k' hexec
  -- `execFullA s (.exerciseA actor target []) = exerciseStepA …` (the §3 reduction); chained-arm commit
  -- ⟹ `exerciseStepA` commits ⟹ `ExerciseHoldSpec` by the executor corner.
  rw [execFullA_exercise_nil] at harm
  exact (exerciseStepA_iff_holdSpec s _ actor target).mp harm

#assert_axioms exerciseStmt_to_holdSpec

/-! ## §4 — THE WELD: a satisfying witness of the audited runnable descriptor agrees, PER CELL, with the
FROZEN balance the IR term's executor produces — carrying the explicit NONCE-TICK divergence.

The SAME shape as the other per-cell welds: route the circuit side through the audited
`exerciseDescriptor_full_sound` (`EffectVmEmitExercise §8`: a satisfying row forces the per-cell
`ExerciseCellSpec` — economic block FROZEN, nonce TICKED) + the connector
`descriptor_agrees_with_executor_exercise` (the descriptor's post-`balLo` AGREES with the executor's
projected post-balance, the FROZEN dimension), and the executor side through §3a (`interp` ⟹
`ExerciseHoldSpec`). The NONCE-TICK divergence (descriptor ticks; executor freezes) is left as an EXPLICIT
conjunct — the honest cap-exercise boundary, reconciled at the turn layer (cited, not re-proved). -/

/-- The circuit interpretation of the exercise IR term: the AUDITED runnable hold-layer descriptor
`exerciseVmDescriptor` (the per-row passthrough gates + nonce TICK + commitment, `EffectVmEmitExercise
§2`). The `exercise`-keyed analog of `compileDropRef = dropRefVmDescriptorGenuine`. -/
def compileExercise : Dregg2.Circuit.Emit.EffectVmEmit.EffectVmDescriptor := exerciseVmDescriptor

/-- **`compileExercise_eq` — `compileExercise` IS the audited runnable exercise descriptor.**
Definitional. -/
theorem compileExercise_eq : compileExercise = exerciseVmDescriptor := rfl

#assert_axioms compileExercise_eq

/-- **`exercise_compile_sound` — the welded soundness (exercise slice, the cap-exercise hold layer).**

Suppose, for the Argus exercise term `exerciseStmt actor target`:
  * the circuit `compileExercise` (= the audited runnable `exerciseVmDescriptor`) is SATISFIED by
    `(env, true, true)` under the abstract Poseidon carrier `hash` on a row with `s_noop = 0` (`hnoop`,
    the non-NoOp exercise row), and its `RowEncodesExercise` decoding NAMES the cell `(pre, post)`
    transition (`henc`), with the pre-`bal_lo` column reading the executor's projected balance of any
    cell `c` (`hpreBal`);
  * the IR term's KERNEL executor interpretation COMMITS: `interp (exerciseStmt actor target) s.kernel =
    some k'` (`hexec`) — i.e. the actor HOLDS the cap-edge.

Then:
  * **frozen-frame leg (per-cell):** the circuit's pinned post-state `post` FREEZES the whole economic
    block relative to `pre` — `balLo`/`balHi`/the 8 `fields`/`capRoot`/`reserved` (the cap-exercise HOLD
    layer moves no value), via the audited `ExerciseCellSpec`;
  * **agreement leg (per-cell):** the circuit's pinned post-`balLo` AGREES — as a field-element congruence
    `≡ [ZMOD p]` on the canonical `bal_lo` column — with the EXECUTOR's projected post-balance
    `balProj s'.kernel c` (here `= balProj s.kernel c`, the executor's frozen kernel), via the connector
    `descriptor_agrees_with_executor_exercise`. So the circuit binds the conserved balance the IR term's
    executor produces;
  * **the NONCE-TICK divergence (explicit, mod `p`):** `post.nonce ≡ pre.nonce + 1 [ZMOD p]` — the descriptor row TICKS the
    cell nonce, while the executor's hold-step FREEZES the kernel (nonce included). This is the same
    structural divergence transfer/burn carry; on the hold layer it is left EXPLICIT (reconciled at the
    turn level by the prologue's single tick, `Argus.Nonce.perEffect_nonce_reconciles_to_turn`, cited).

So the runnable circuit the prover runs for the cap-exercise hold layer pins the per-cell FROZEN economic
frame that the IR term's executor produces, agrees on the conserved balance, and ticks the nonce ONCE (the
runtime row-bookkeeping leg) — the per-effect refinement for dregg1's `ExerciseViaCapability` outer layer.

NOTE (the scope): both legs pertain to the OUTER hold-gate layer (`inner = []`). The inner
sub-forest (R4 facet-mask + the `execInnerA` fold) is the turn-composition layer; its conservation is the
summed inner deltas (`Handlers.Exercise.exercise_conserves`) and each inner effect's own per-row
descriptor — cited, OUT of this weld (§DEFER). -/
theorem exercise_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (s : RecChainedState) (actor target c : CellId) (k' : RecordKernelState)
    (pre post : CellState)
    (hnoop : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sel.NOOP = 0)
    (hpreBal : env.loc (Dregg2.Circuit.Emit.EffectVmEmit.sbCol
                 Dregg2.Circuit.Emit.EffectVmEmit.state.BALANCE_LO) = balProj s.kernel c)
    (henc : RowEncodesExercise env pre post)
    (hgatesat : satisfiedVm hash compileExercise env true false)
    (hsat : satisfiedVm hash compileExercise env true true)
    (hexec : interp (exerciseStmt actor target) s.kernel = some k') :
    -- frozen-frame leg: the whole economic block is frozen at the hold layer (pre ≡ post on bal/fields/…) …
    ( ExerciseCellSpec pre post )
    -- … the agreement leg: the descriptor's post-`balLo` IS the executor's committed (frozen) post-balance
    --   `balProj k' c` (the kernel `interp`/`exerciseStepA` produces), as a FIELD-ELEMENT congruence
    --   (`≡ [ZMOD p]` — the circuit pins field elements on the canonical `bal_lo` column) …
    ∧ ( post.balLo ≡ balProj k' c [ZMOD 2013265921] )
    -- … and the EXPLICIT nonce-tick divergence (mod `p`): the row ticks the cell nonce; the executor
    --   freezes it. The pin is the field congruence on the canonical `nonce` column.
    ∧ ( post.nonce ≡ pre.nonce + 1 [ZMOD 2013265921] ) := by
  -- circuit side: the audited descriptor soundness forces the per-cell `ExerciseCellSpec` (frame freeze +
  -- nonce tick) on this `s_noop = 0` exercise row.
  rw [compileExercise_eq] at hsat hgatesat
  obtain ⟨hcs, _hcommit⟩ := exerciseDescriptor_full_sound hash env pre post hnoop henc hgatesat hsat
  -- executor side: the IR-term commit yields the connector's `ExerciseHoldSpec` (§3a) on the chained
  -- post-state `s' = ⟨k', authReceipt actor :: s.log⟩` (whose kernel is `k'`).
  have hhold : ExerciseHoldSpec s actor target { kernel := k', log := authReceipt actor :: s.log } :=
    exerciseStmt_to_holdSpec s actor target k' hexec
  -- the connector welds the descriptor's frozen `balLo` against the executor's projected post-balance
  -- `balProj s'.kernel c` = `balProj k' c` (the chained state's kernel IS `k'`).
  have hagree : post.balLo ≡ balProj k' c [ZMOD 2013265921] :=
    descriptor_agrees_with_executor_exercise hash env hnoop s
      { kernel := k', log := authReceipt actor :: s.log } actor target c pre post
      hpreBal henc hgatesat hsat hhold
  -- the nonce-tick conjunct is the THIRD clause of `ExerciseCellSpec` (`post.nonce = pre.nonce + 1`).
  exact ⟨hcs, hagree, hcs.2.2.1⟩

#assert_axioms exercise_compile_sound

/-! ## §5 — NON-VACUITY: the term GATES on the held cap-edge (admit/reject two-valued), freezes
the kernel, and the descriptor is the genuine runnable circuit (not a placeholder). The cornerstone/weld
would be hollow if `exerciseStmt` admitted everything, mutated the kernel, or rode an inert descriptor. -/

/-- A two-account kernel where holder `0` holds a single `node 7` cap (an edge to target `7`), holder `1`
holds nothing. (Cell `0` Live; accounts `{0,1}`.) Reuses the `kDrop`-shape cap fixture. -/
def kEx : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 7] else [] }

/-- **`exerciseStmt_admits_held` — the hold-gate ADMITS a held edge (the kernel UNCHANGED).**
Holder `0` exercising its `node 7` cap to target `7` COMMITS, returning the kernel VERBATIM (`some kEx`) —
the cap-exercise hold layer reads the c-list and freezes the kernel (no value moves, no edge changes). The
admitting half of the two-valued gate, and the kernel-freeze the weld pins. -/
theorem exerciseStmt_admits_held :
    interp (exerciseStmt 0 7) kEx = some kEx := by
  show (if exerciseGuardB 0 7 kEx = true then some kEx else none) = some kEx
  rw [if_pos]
  decide

/-- **`exerciseStmt_rejects_unheld` — the hold-gate REJECTS a missing edge (fail-closed).** Holder `1`,
who holds NO cap conferring an edge to `7`, CANNOT exercise — the term returns `none` (the `confersEdgeTo`
hold-gate fails closed). Only the holder of the cap may exercise it; the rejecting half of the gate. -/
theorem exerciseStmt_rejects_unheld :
    interp (exerciseStmt 1 7) kEx = none := by
  show (if exerciseGuardB 1 7 kEx = true then some kEx else none) = none
  rw [if_neg]
  decide

/-- **`exerciseStmt_rejects_wrong_target` — the hold-gate is TARGET-SPECIFIC (fail-closed).** Holder `0`
holds an edge to `7`, but NOT to `8`; exercising a cap to target `8` returns `none` (no held edge to `8`).
So the gate binds the SPECIFIC `target`, not merely "holds some cap" — a third non-vacuity witness. -/
theorem exerciseStmt_rejects_wrong_target :
    interp (exerciseStmt 0 8) kEx = none := by
  show (if exerciseGuardB 0 8 kEx = true then some kEx else none) = none
  rw [if_neg]
  decide

/-- **`exerciseStmt_frozen_kernel` — the kernel is FROZEN on a committing exercise.** When the hold-gate
admits, the post-kernel IS the input (the §guard domain-restrictor never mutates) — the cap-exercise hold
layer changes no kernel field, exactly the freeze the descriptor pins (mod the runtime nonce-tick the weld
carries explicitly). -/
theorem exerciseStmt_frozen_kernel (actor target : CellId) (k k' : RecordKernelState)
    (h : interp (exerciseStmt actor target) k = some k') : k' = k := by
  simp only [exerciseStmt, interp] at h
  by_cases hg : exerciseGuardB actor target k = true
  · rw [if_pos hg] at h; exact (Option.some.injEq _ _).mp h.symm
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`compileExercise_nontrivial` — the welded circuit is the genuine runnable descriptor, not a
placeholder.** `exerciseVmDescriptor` carries the 13 row-gates + 14 transition + 4 boundaryFirst + 3
boundaryLast + 1 selector = 35 constraints AND 4 GROUP-4 commitment hash-sites (an inert placeholder would
have 0/0). So `exercise_compile_sound` is a statement about a REAL runnable circuit. -/
theorem compileExercise_nontrivial :
    compileExercise.constraints.length = 35
    ∧ compileExercise.hashSites.length = 4 := by
  rw [compileExercise_eq]
  refine ⟨by decide, by decide⟩

#assert_axioms exerciseStmt_admits_held
#assert_axioms exerciseStmt_rejects_unheld
#assert_axioms exerciseStmt_rejects_wrong_target
#assert_axioms exerciseStmt_frozen_kernel
#assert_axioms compileExercise_nontrivial

/-! ## §MAGNESIUM — THE RUNNABLE full-state soundness (all 17 fields + the 8 side-table roots, on the
circuit the prover RUNS).

§4 welded the Argus term against the audited runnable descriptor `exerciseVmDescriptor` on the PER-CELL
surface (`exerciseDescriptor_full_sound`: the cell's economic block FROZEN, nonce TICKED). This section
adds the FULL-STATE upgrade: the WIDE runnable descriptor `exerciseVmDescriptorWide` (the 188-wide
`system_roots`-absorbing EffectVM descriptor) pins the FULL 17-field declarative post-state — the per-cell
economic block FROZEN + the nonce TICKED (via the absorbed columns) AND ALL 8 side-table roots FROZEN (via
the wide commitment). This closes the Class-C "pale ghost" on the runnable descriptor: the narrow 186-wide
`exerciseVmDescriptor`'s commitment bound NONE of the 8 side-table roots; the wide one binds them.

RESIDUALS (carried, NOT papered — the SAME boundaries §4/§DEFER name): the OUTER hold-gate layer
(`inner = []`); the NONCE-TICK divergence (the runtime row ticks the cell nonce — `post.nonce = pre.nonce
+ 1` — while the executor hold-step FREEZES the kernel, reconciled at the turn level); the receipt-log
prepend (off the per-row state block, riding universe-A's portal). This module closes ONLY the
side-table-root binding gap on the kernel state — the inner sub-forest stays the turn-composition layer. -/

open Dregg2.Circuit.Emit.EffectVmEmitExercise (RowEncodesExercise ExerciseCellSpec)
open Dregg2.Circuit.Emit.EffectVmEmitExerciseWide
  (exerciseVmDescriptorWide exercise_runnable_full_sound)
open Dregg2.Exec.SystemRoots (SysRoots)

/-- **`exercise_runnable_full_state_weld` — THE RUNNABLE full-state soundness (exercise hold-layer slice).**
A row satisfying the RUNNABLE wide descriptor `exerciseVmDescriptorWide` (`satisfiedVm`, first/last
active), decoded by `RowEncodesExercise env pre post` with the frozen-roots witness `sr = preRoots`, pins
the FULL 17-field declarative post-state: the per-cell `ExerciseCellSpec` (economic block FROZEN, nonce
TICKED) AND all 8 side-table roots FROZEN (`sr = preRoots`). This is the FULL-STATE strengthening of §4's
per-cell `exercise_compile_sound` — and it BINDS the side-table roots the narrow descriptor left unbound.
The per-cell economic freeze IS the frozen kernel the IR term's executor produces (§4); the nonce-tick +
receipt-log are the carried turn-level residuals named above. -/
theorem exercise_runnable_full_state_weld
    (hash : List ℤ → ℤ) (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (pre post : CellState) (sr preRoots : SysRoots)
    (hrow : Dregg2.Circuit.Emit.EffectVmEmitExercise.IsExerciseRow env)
    (henc : RowEncodesExercise env pre post) (hroots : sr = preRoots)
    (hsat : Dregg2.Circuit.Emit.EffectVmEmit.satisfiedVm hash exerciseVmDescriptorWide env true false) :
    ExerciseCellSpec pre post ∧ sr = preRoots :=
  exercise_runnable_full_sound hash env pre post sr preRoots hrow henc hroots hsat

#assert_axioms exercise_runnable_full_state_weld

/-! ## §DEFER — scope of this weld (documented, NOT a silent gap).

  * **The INNER sub-forest is OUT of this per-effect weld.** This module pins the OUTER hold-gate layer
    (the bare cap-exercise, `inner = []`) — exactly the layer the audited descriptor connector speaks
    about. The R4 facet-mask + the `execInnerA` fold over `inner` is the TURN-COMPOSITION layer: each
    inner effect is its OWN per-row descriptor, composed through `TurnEmit`, and the summed-delta
    conservation is the algebra twin `Handlers.Exercise.exercise_conserves` — cited, not re-claimed here.

  * **The NONCE-TICK divergence is carried, not closed.** The executor hold-step FREEZES the kernel; the
    runtime EffectVM row TICKS the cell nonce. `exercise_compile_sound` exposes `post.nonce = pre.nonce +
    1` as an EXPLICIT conjunct; the turn-level reconciliation (the prologue's single tick) is
    `Argus.Nonce.perEffect_nonce_reconciles_to_turn`, cited — not re-proved in this per-effect module.

  * **PER-CELL, not full-state `Surface2`.** The exercise hold layer has no standalone `Surface2`/
    `EffectCommit2 *_full_sound` (its genuine content is connectivity / non-amplification — the AUTHORITY
    regime `EffectsAuthority.exercise_non_amplifying`, the cap graph UNCHANGED — and the conserved frozen
    frame, not a value/side-table move). So the weld lives on the per-cell `cellProj`/`balProj` surface
    the runnable descriptor supports, exactly like transfer/delegate, not the whole-state digest surface.
-/

end Dregg2.Circuit.Argus.Effects.ExerciseViaCapability
