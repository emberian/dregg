/-
# Dregg2.Circuit.Emit.BilateralAggregationRefine — the RUNG-1 functional-correctness refinement for
the emitted BILATERAL-BUNDLE AGGREGATION descriptor (`bilateralAggDescriptor`).

## What this file IS

`EffectVmEmitBilateralAgg.lean` / `BilateralAggregationEmit.lean` prove only PER-GATE faithfulness
(`cg3_body_zero_iff` — one gate poly = 0 ↔ its LOCAL relation — plus the boundary/identity teeth
`agg_rejects_turn_mismatch` / `agg_rejects_bad_agent_count` over the per-window `aggWindowHolds`).
This file proves the missing WHOLE-DESCRIPTOR bridge: a trace SATISFYING the emitted descriptor via
the DEPLOYED acceptance predicate `DescriptorIR2.Satisfied2` corresponds to the GENUINE semantic
relation the aggregation AIR is meant to compute — a valid bilateral-bundle aggregation:

  * (CG-2 turn binding) the bundle's FIRST and LAST cell carry the published outer-PI turn identity;
  * (CG-3 schedule replay) every NON-FINAL cell's carried counts/roots equal its `expected_*` columns
    (the CG-3 gate is a `when_transition` gate — its faithful Lean denotation `.base (.gate _)` is
    vacuous on the last row, the transition-zerofier lowering, so replay is stated on cells `0…n-2`);
  * (CG-4 accounting — THE CROWN) EXACTLY ONE agent cell across the whole bundle
    (`∑ is_agent = 1`), and the published `n_cells` equals the number of consistent cells
    (`pi[N_CELLS] = ∑ consistent`) — both proven by threading the two cumulative-sum `windowGate`
    recurrences from the row-0 seeds to the last-row boundaries (the running-sum induction
    `running_sum`, the genuine "aggregation" content).

## The semantic relation

No separate whole-trace semantic MODEL existed for this family (the census `lean_spec` is the emit
files themselves); so we AUTHOR the functional spec `BundleAggregated t` (§2) and prove
`Satisfied2 … → BundleAggregated t` (SAT_IMPLIES_SEM) in `bilateralAgg_refines` (§5).

## Field-faithful denotation

`VmConstraint.holdsVm`/`WindowConstraint.holdsAt` pin every gate only `≡ 0 [ZMOD p]`
(`p = 2013265921`, BabyBear) — the DEPLOYED field constraint, not a ℤ toy. The bridge therefore
threads the EXPLICIT canonicality envelope `AggTraceCanon` (§2.5: every cell/PI a canonical
representative in `[0, p)`, plus last-row booleanity of the two contribution columns — the one row
where the AIR's own boolean gates are vacuous) and a bundle-size bound `|rows| < p`. Under it the
crown is recovered EXACTLY over ℤ (`running_sum_canon` — the strengthened induction
`cum j = prefixSum j ≤ j + 1 < p`, so no wrap-around forgery of the agent count is possible); the
envelope is inhabited concretely by `witTrace_canon` (§6), so it is not vacuous.

## Non-vacuity

`witTrace` (§6): a concrete 2-row bundle `cell0 (non-agent, consistent) · cell1 (the agent cell)`
that PROVABLY `Satisfied2 bilateralAggDescriptor` — feeding it the bridge recovers the genuine
aggregation (`∑ is_agent = 1`, `pi[N_CELLS] = 2 = ∑ consistent`), exercising BOTH cumulative
recurrences and the schedule replay on the non-last cell. `badTrace`: a trace whose last-row
cumulative ≠ 1 that PROVABLY fails `Satisfied2` (`badTrace_not_satisfied` — the single-agent boundary
bites). So the `Satisfied2` hypothesis is genuinely inhabited AND constraining.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The bridge is CRYPTO-FREE: the
descriptor declares no tables/hash-sites/ranges/map-ops, so no Poseidon2 carrier enters. NEW file;
imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg

namespace Dregg2.Circuit.Emit.BilateralAggregationRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv VmRow holdsVm_boundaryFirst_true holdsVm_boundaryLast_true
   holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt gate_modEq_iff)

set_option autoImplicit false

/-! ## §0 — The running (prefix) sum and its determination from a seed + step recurrence. -/

/-- The prefix sum `f 0 + f 1 + … + f n` (the sum of the first `n+1` terms). -/
def prefixSum (f : Nat → ℤ) : Nat → ℤ
  | 0     => f 0
  | n + 1 => prefixSum f n + f (n + 1)

/-- **A cumulative column that is SEEDED (`cumf 0 = contribf 0`) and STEPPED
(`cumf (i+1) = cumf i + contribf (i+1)` on every transition) equals the prefix sum of its
contributions.** The pure arithmetic core of the aggregation crown — a running-sum induction. -/
theorem running_sum (len : Nat) (cumf contribf : Nat → ℤ)
    (hseed : cumf 0 = contribf 0)
    (hstep : ∀ i, i + 1 < len → cumf (i + 1) = cumf i + contribf (i + 1)) :
    ∀ j, j < len → cumf j = prefixSum contribf j := by
  intro j
  induction j with
  | zero => intro _; simpa only [prefixSum] using hseed
  | succ n ih =>
      intro hlt
      have hn : n < len := by omega
      simp only [prefixSum]
      rw [hstep n hlt, ih hn]

/-- Prefix sums of BOOLEAN contributions are bounded: `0 ≤ prefixSum f j ≤ j + 1`. The size half of
the field-faithful crown recovery — a boolean-fed cumulative cannot reach the modulus on a bundle
shorter than `p`. -/
theorem prefixSum_bool_bounds (contribf : Nat → ℤ) :
    ∀ j, (∀ m, m ≤ j → contribf m = 0 ∨ contribf m = 1) →
      0 ≤ prefixSum contribf j ∧ prefixSum contribf j ≤ (j : ℤ) + 1 := by
  intro j
  induction j with
  | zero =>
      intro h
      rcases h 0 (Nat.le_refl 0) with h0 | h0 <;> simp only [prefixSum, h0] <;> norm_num
  | succ n ih =>
      intro h
      have ihn := ih (fun m hm => h m (Nat.le_succ_of_le hm))
      rcases h (n + 1) (Nat.le_refl _) with h1 | h1 <;>
        simp only [prefixSum, h1] <;> push_cast <;> omega

/-- **The FIELD-FAITHFUL running-sum determination.** The deployed AIR pins the seed/step only
`≡ [ZMOD p]`; with the cumulative column CANONICAL (`0 ≤ · < p`, the range-check invariant),
BOOLEAN contributions, and a bundle SHORTER than `p`, the mod-`p` recurrence still determines the
exact ℤ prefix sum — the strengthened induction carries `cumf j = prefixSum j ≤ j + 1 < p`, so each
congruence collapses to an equality and no wrap-around forgery of the count is possible. -/
theorem running_sum_canon (len : Nat) (hlen : (len : ℤ) < 2013265921)
    (cumf contribf : Nat → ℤ)
    (hcanon : ∀ j, 0 ≤ cumf j ∧ cumf j < 2013265921)
    (hbool : ∀ j, j < len → contribf j = 0 ∨ contribf j = 1)
    (hseed : cumf 0 ≡ contribf 0 [ZMOD 2013265921])
    (hstep : ∀ i, i + 1 < len → cumf (i + 1) ≡ cumf i + contribf (i + 1) [ZMOD 2013265921]) :
    ∀ j, j < len → cumf j = prefixSum contribf j := by
  intro j
  induction j with
  | zero =>
      intro hj
      obtain ⟨k, hk⟩ := hseed.dvd
      have hc := hcanon 0
      rcases hbool 0 hj with h0 | h0 <;> simp only [prefixSum] <;> omega
  | succ n ih =>
      intro hj
      have hn : n < len := by omega
      have ihn := ih hn
      obtain ⟨k, hk⟩ := (hstep n hj).dvd
      have hc := hcanon (n + 1)
      have hps := prefixSum_bool_bounds contribf n (fun m hm => hbool m (by omega))
      rcases hbool (n + 1) hj with h1 | h1 <;> simp only [prefixSum] <;> omega

/-! ## §1 — Row accessors (the `loc` environment of each trace row). -/

/-- Row `i`'s assignment (the current-row `loc` slice of the row window at `i`). -/
def rowAt (t : VmTrace) (i : Nat) : Assignment := (envAt t i).loc

/-- The agent-cell flag of row `i`. -/
def isAgentAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i (Agg.schCol Sched.IS_AGENT_CELL)
/-- The per-row consistency indicator of row `i`. -/
def consistentAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i Agg.CONSISTENT_INDICATOR_COL
/-- The running `is_agent` cumulative at row `i`. -/
def cumAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i Agg.IS_AGENT_CUMULATIVE_COL
/-- The running active-cell counter at row `i`. -/
def nActiveAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i Agg.N_CELLS_ACTIVE_COL

/-! ## §2 — The GENUINE semantic relation: a valid bilateral-bundle aggregation. -/

/-- **`BundleAggregated t`** — what an accepting bilateral-aggregation trace MEANS: the bundle's cells
share the published turn identity (bound at both ends), each non-final cell faithfully replays its
bilateral schedule, EXACTLY ONE cell is the agent cell across the bundle, and the published
`n_cells` equals the number of consistent cells. This is the functional-correctness spec the emitted
descriptor is proven to refine. -/
structure BundleAggregated (t : VmTrace) : Prop where
  /-- The bundle is non-empty. -/
  nonempty : 0 < t.rows.length
  -- CG-2: the FIRST cell carries the published turn identity (13 felts: turn-hash · effects-hash ·
  -- actor-nonce · previous-receipt).
  turnHashFirst : ∀ i < OuterPi.TURN_HASH_LEN,
      rowAt t 0 (Agg.schCol (Sched.TURN_HASH_BASE + i)) = t.pub (OuterPi.TURN_HASH_BASE + i)
  effectsFirst : ∀ i < OuterPi.EFFECTS_HASH_GLOBAL_LEN,
      rowAt t 0 (Agg.schCol (Sched.EFFECTS_HASH_GLOBAL_BASE + i))
        = t.pub (OuterPi.EFFECTS_HASH_GLOBAL_BASE + i)
  actorNonceFirst : rowAt t 0 (Agg.schCol Sched.ACTOR_NONCE) = t.pub OuterPi.ACTOR_NONCE
  prevReceiptFirst : ∀ i < OuterPi.PREVIOUS_RECEIPT_HASH_LEN,
      rowAt t 0 (Agg.schCol (Sched.PREVIOUS_RECEIPT_HASH_BASE + i))
        = t.pub (OuterPi.PREVIOUS_RECEIPT_HASH_BASE + i)
  -- CG-2: the LAST cell carries the SAME published turn identity.
  turnHashLast : ∀ i < OuterPi.TURN_HASH_LEN,
      rowAt t (t.rows.length - 1) (Agg.schCol (Sched.TURN_HASH_BASE + i))
        = t.pub (OuterPi.TURN_HASH_BASE + i)
  effectsLast : ∀ i < OuterPi.EFFECTS_HASH_GLOBAL_LEN,
      rowAt t (t.rows.length - 1) (Agg.schCol (Sched.EFFECTS_HASH_GLOBAL_BASE + i))
        = t.pub (OuterPi.EFFECTS_HASH_GLOBAL_BASE + i)
  actorNonceLast : rowAt t (t.rows.length - 1) (Agg.schCol Sched.ACTOR_NONCE) = t.pub OuterPi.ACTOR_NONCE
  prevReceiptLast : ∀ i < OuterPi.PREVIOUS_RECEIPT_HASH_LEN,
      rowAt t (t.rows.length - 1) (Agg.schCol (Sched.PREVIOUS_RECEIPT_HASH_BASE + i))
        = t.pub (OuterPi.PREVIOUS_RECEIPT_HASH_BASE + i)
  -- CG-3: every NON-FINAL cell replays its schedule (7 counts + 28 root felts) against the
  -- prover-populated `expected_*` columns.
  replayCounts : ∀ i, i + 1 < t.rows.length → ∀ k < Sched.COUNTS_LEN,
      rowAt t i (Agg.schCol (Sched.COUNTS_BASE + k)) = rowAt t i (Agg.EXPECTED_COUNTS_BASE + k)
  replayRoots : ∀ i, i + 1 < t.rows.length → ∀ k < Sched.ROOTS_LEN,
      rowAt t i (Agg.schCol (Sched.ROOTS_BASE + k)) = rowAt t i (Agg.EXPECTED_ROOTS_BASE + k)
  -- CG-4 (the crown): exactly ONE agent cell across the bundle; published n_cells = # consistent.
  exactlyOneAgent : prefixSum (isAgentAt t) (t.rows.length - 1) = 1
  publishedCount : t.pub OuterPi.N_CELLS = prefixSum (consistentAt t) (t.rows.length - 1)

/-! ## §2.5 — The canonicality envelope (the deployed range-check invariant, explicit).

The field-faithful denotation pins gates only `≡ 0 [ZMOD p]`; the ℤ reading is honest exactly
because deployed traces carry canonical representatives. Booleanity of the two CG-4 contribution
columns is DERIVED from the descriptor's own boolean gates on every non-last row
(`isAgent_cases`/`consistent_cases` in §4); only the LAST row — where a `.gate` is vacuous under
the transition-zerofier lowering — needs it as an envelope hypothesis. -/

/-- Two canonical representatives congruent mod `p` are EQUAL (`p ∣ residual` with
`residual ∈ (−p, p)` collapses to `0`). -/
theorem eq_of_modEq_of_canon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (ha1 : a < 2013265921) (hb0 : 0 ≤ b) (hb1 : b < 2013265921) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  omega

/-- A canonical cell whose booleanity gate vanishes mod `p` IS `0` or `1` over ℤ: primality splits
`p ∣ x·(x−1)`, and canonicality collapses each factor.

⚑ **CANONICAL SHAPE.** `GateExpr.gBoolCanon`'s rendering evaluates to `1·(x·x) + (−1)·x`, not
`x·(x−1)` — the SAME polynomial (`ring`), a DIFFERENT `EmittedExpr` tree (9 nodes, the corpus
normal form). The hypothesis is stated at that shape (what every migrated call site now produces
after unfolding its `boolGate_eq`); the `ring`-bridge to the factored form is internal. -/
theorem bool_of_boolGate {x : ℤ} (h : 1 * (x * x) + -1 * x ≡ 0 [ZMOD 2013265921])
    (h0 : 0 ≤ x) (h1 : x < 2013265921) : x = 0 ∨ x = 1 := by
  have h' : x * (x + (-1)) ≡ 0 [ZMOD 2013265921] := by
    have e : (1 : ℤ) * (x * x) + -1 * x = x * (x + (-1)) := by ring
    rwa [e] at h
  have hd : (2013265921 : ℤ) ∣ x * (x + (-1)) := Int.modEq_zero_iff_dvd.mp h'
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-- **The aggregation canonicality envelope**: every trace cell and public input is a canonical
BabyBear representative (`0 ≤ · < p`), and the two CG-4 contribution columns are boolean on the
LAST row (the one row where the AIR's boolean gates are vacuous). Inhabited by `witTrace_canon`. -/
structure AggTraceCanon (t : VmTrace) : Prop where
  cells : ∀ i c, 0 ≤ rowAt t i c ∧ rowAt t i c < 2013265921
  pubs : ∀ k, 0 ≤ t.pub k ∧ t.pub k < 2013265921
  lastAgentBool :
    isAgentAt t (t.rows.length - 1) = 0 ∨ isAgentAt t (t.rows.length - 1) = 1
  lastConsistentBool :
    consistentAt t (t.rows.length - 1) = 0 ∨ consistentAt t (t.rows.length - 1) = 1

/-! ## §3 — The consumed constraints are genuinely present in the descriptor. -/

theorem mem_firstCumSeed : firstCumSeed ∈ bilateralAggDescriptor.constraints := by
  show firstCumSeed ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem mem_firstNSeed : firstNSeed ∈ bilateralAggDescriptor.constraints := by
  show firstNSeed ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem mem_lastCumIsOne : lastCumIsOne ∈ bilateralAggDescriptor.constraints := by
  show lastCumIsOne ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem mem_lastNEqPi : lastNEqPi ∈ bilateralAggDescriptor.constraints := by
  show lastNEqPi ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem mem_boolIsAgent : boolGate (Agg.schCol Sched.IS_AGENT_CELL)
    ∈ bilateralAggDescriptor.constraints := by
  show boolGate _ ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem mem_boolConsistent : boolGate Agg.CONSISTENT_INDICATOR_COL
    ∈ bilateralAggDescriptor.constraints := by
  show boolGate _ ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem mem_cumAgentTransition : cumAgentTransition ∈ bilateralAggDescriptor.constraints := by
  show cumAgentTransition ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem mem_cumActiveTransition : cumActiveTransition ∈ bilateralAggDescriptor.constraints := by
  show cumActiveTransition ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem mem_scheduleReplay_counts (k : Nat) (hk : k < Sched.COUNTS_LEN) :
    cg3Eq (Agg.schCol (Sched.COUNTS_BASE + k)) (Agg.EXPECTED_COUNTS_BASE + k)
      ∈ bilateralAggDescriptor.constraints := by
  show _ ∈ aggConstraints; unfold aggConstraints
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  unfold scheduleReplay
  exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr hk))

theorem mem_scheduleReplay_roots (k : Nat) (hk : k < Sched.ROOTS_LEN) :
    cg3Eq (Agg.schCol (Sched.ROOTS_BASE + k)) (Agg.EXPECTED_ROOTS_BASE + k)
      ∈ bilateralAggDescriptor.constraints := by
  show _ ∈ aggConstraints; unfold aggConstraints
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  unfold scheduleReplay
  exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hk))

/-- A first-row turn binding is in `turnIdBindings .first`; a last-row one in `turnIdBindings .last`. -/
theorem mem_A {c : VmConstraint2} (h : c ∈ turnIdBindings .first) :
    c ∈ bilateralAggDescriptor.constraints := by
  show c ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ h)))

theorem mem_B {c : VmConstraint2} (h : c ∈ turnIdBindings .last) :
    c ∈ bilateralAggDescriptor.constraints := by
  show c ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h)))

theorem mem_turn_hash (row : VmRow) (i : Nat) (hi : i < OuterPi.TURN_HASH_LEN) :
    cg2PiBind row (Agg.schCol (Sched.TURN_HASH_BASE + i)) (OuterPi.TURN_HASH_BASE + i)
      ∈ turnIdBindings row := by
  unfold turnIdBindings
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map_of_mem (List.mem_range.mpr hi))))

theorem mem_turn_effects (row : VmRow) (i : Nat) (hi : i < OuterPi.EFFECTS_HASH_GLOBAL_LEN) :
    cg2PiBind row (Agg.schCol (Sched.EFFECTS_HASH_GLOBAL_BASE + i))
        (OuterPi.EFFECTS_HASH_GLOBAL_BASE + i) ∈ turnIdBindings row := by
  unfold turnIdBindings
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (List.mem_range.mpr hi))))

theorem mem_turn_nonce (row : VmRow) :
    cg2PiBind row (Agg.schCol Sched.ACTOR_NONCE) OuterPi.ACTOR_NONCE ∈ turnIdBindings row := by
  unfold turnIdBindings
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

theorem mem_turn_prev (row : VmRow) (i : Nat) (hi : i < OuterPi.PREVIOUS_RECEIPT_HASH_LEN) :
    cg2PiBind row (Agg.schCol (Sched.PREVIOUS_RECEIPT_HASH_BASE + i))
        (OuterPi.PREVIOUS_RECEIPT_HASH_BASE + i) ∈ turnIdBindings row := by
  unfold turnIdBindings
  exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hi))

/-! ## §4 — Extraction: read the per-row facts out of a `Satisfied2` witness. -/

section Extract

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **A base-gate constraint forces its body to vanish mod `p` on a NON-LAST row** (a `.gate` is
vacuous on the last row — the transition-zerofier lowering; the field-faithful denotation pins
only the congruence, the ℤ readings live under `AggTraceCanon`). -/
theorem gate_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t) {i : Nat}
    (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    {g : EmittedExpr} (hg : VmConstraint2.base (.gate g) ∈ bilateralAggDescriptor.constraints) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i hi _ hg
  have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
  simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- **An `onTransition` window constraint forces its body to vanish mod `p` on a NON-LAST row.** -/
theorem window_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t) {i : Nat}
    (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    {w : WindowConstraint} (hw : VmConstraint2.windowGate w ∈ bilateralAggDescriptor.constraints)
    (honT : w.onTransition = true) :
    w.body.eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i hi _ hw
  have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, honT, if_true] at hrc
  exact hrc hlf

/-- **A first-row PI binding fires on the first row** (mod `p` — the field-faithful pin). -/
theorem piFirst_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {col k : Nat}
    (hb : VmConstraint2.base (.piBinding .first col k) ∈ bilateralAggDescriptor.constraints) :
    (envAt t 0).loc col ≡ t.pub k [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints 0 hpos _ hb
  exact (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) col k).mp hrc

/-- **A last-row PI binding fires on the last row** (mod `p` — the field-faithful pin). -/
theorem piLast_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {col k : Nat}
    (hb : VmConstraint2.base (.piBinding .last col k) ∈ bilateralAggDescriptor.constraints) :
    (envAt t (t.rows.length - 1)).loc col ≡ t.pub k [ZMOD 2013265921] := by
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hrc := hsat.rowConstraints (t.rows.length - 1) hlt _ hb
  have hlast_true : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hpos]; exact beq_self_eq_true _
  rw [hlast_true] at hrc
  exact (holdsVm_piLast_true (envAt t (t.rows.length - 1)) (t.rows.length - 1 == 0) col k).mp hrc

/-- **A first-row boundary forces its body to vanish mod `p` on the first row.** -/
theorem boundaryFirst_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {b : EmittedExpr}
    (hb : VmConstraint2.base (.boundary .first b) ∈ bilateralAggDescriptor.constraints) :
    b.eval (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints 0 hpos _ hb
  exact (holdsVm_boundaryFirst_true (envAt t 0) (0 + 1 == t.rows.length) b).mp hrc

/-- **A last-row boundary forces its body to vanish mod `p` on the last row.** -/
theorem boundaryLast_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {b : EmittedExpr}
    (hb : VmConstraint2.base (.boundary .last b) ∈ bilateralAggDescriptor.constraints) :
    b.eval (envAt t (t.rows.length - 1)).loc ≡ 0 [ZMOD 2013265921] := by
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hrc := hsat.rowConstraints (t.rows.length - 1) hlt _ hb
  have hlast_true : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hpos]; exact beq_self_eq_true _
  rw [hlast_true] at hrc
  exact (holdsVm_boundaryLast_true (envAt t (t.rows.length - 1)) (t.rows.length - 1 == 0) b).mp hrc

/-- Canonicality reading of a PI pin: a cell congruent to a public input IS it (both canonical). -/
theorem cellPub_eq (hcanon : AggTraceCanon t) {i col k : Nat}
    (h : (envAt t i).loc col ≡ t.pub k [ZMOD 2013265921]) : rowAt t i col = t.pub k :=
  eq_of_modEq_of_canon h (hcanon.cells i col).1 (hcanon.cells i col).2
    (hcanon.pubs k).1 (hcanon.pubs k).2

/-- Canonicality reading of a cell-equality gate: two congruent canonical cells are EQUAL. -/
theorem cellCell_eq (hcanon : AggTraceCanon t) {i a b : Nat}
    (h : (envAt t i).loc a ≡ (envAt t i).loc b [ZMOD 2013265921]) : rowAt t i a = rowAt t i b :=
  eq_of_modEq_of_canon h (hcanon.cells i a).1 (hcanon.cells i a).2
    (hcanon.cells i b).1 (hcanon.cells i b).2

/-- Row-0 seed (mod `p`): `cum ≡ is_agent`. -/
theorem seed_cum_modEq (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) : cumAt t 0 ≡ isAgentAt t 0 [ZMOD 2013265921] := by
  have h := boundaryFirst_forces hsat hpos mem_firstCumSeed
  simp only [EmittedExpr.eval] at h
  simp only [cumAt, isAgentAt, rowAt]
  exact (gate_modEq_iff (by ring)).mp h

/-- Row-0 seed (mod `p`): `n ≡ consistent`. -/
theorem seed_n_modEq (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) : nActiveAt t 0 ≡ consistentAt t 0 [ZMOD 2013265921] := by
  have h := boundaryFirst_forces hsat hpos mem_firstNSeed
  simp only [EmittedExpr.eval] at h
  simp only [nActiveAt, consistentAt, rowAt]
  exact (gate_modEq_iff (by ring)).mp h

/-- Transition (mod `p`): `cum (i+1) ≡ cum i + is_agent (i+1)` (the cumulative recurrence). -/
theorem step_cum_modEq (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t) (i : Nat)
    (hii : i + 1 < t.rows.length) :
    cumAt t (i + 1) ≡ cumAt t i + isAgentAt t (i + 1) [ZMOD 2013265921] := by
  have hi : i < t.rows.length := by omega
  have hnl : i + 1 ≠ t.rows.length := by omega
  have h := window_forces hsat hi hnl mem_cumAgentTransition rfl
  simp only [WindowExpr.eval, envAt] at h
  simp only [cumAt, isAgentAt, rowAt, envAt]
  exact (gate_modEq_iff (by ring)).mp h

/-- Transition (mod `p`): `n (i+1) ≡ n i + consistent (i+1)` (the active-cell recurrence). -/
theorem step_n_modEq (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t) (i : Nat)
    (hii : i + 1 < t.rows.length) :
    nActiveAt t (i + 1) ≡ nActiveAt t i + consistentAt t (i + 1) [ZMOD 2013265921] := by
  have hi : i < t.rows.length := by omega
  have hnl : i + 1 ≠ t.rows.length := by omega
  have h := window_forces hsat hi hnl mem_cumActiveTransition rfl
  simp only [WindowExpr.eval, envAt] at h
  simp only [nActiveAt, consistentAt, rowAt, envAt]
  exact (gate_modEq_iff (by ring)).mp h

/-- Last-row boundary (mod `p`): `cum ≡ 1`. -/
theorem last_cum_modEq (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) : cumAt t (t.rows.length - 1) ≡ 1 [ZMOD 2013265921] := by
  have h := boundaryLast_forces hsat hpos mem_lastCumIsOne
  simp only [EmittedExpr.eval] at h
  simp only [cumAt, rowAt]
  exact (gate_modEq_iff (by ring)).mp h

/-- Last-row boundary over ℤ: `cum = 1` — exactly one agent cell (canonical cell, `1 < p`). -/
theorem last_cum (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) (hcanon : AggTraceCanon t) :
    cumAt t (t.rows.length - 1) = 1 :=
  eq_of_modEq_of_canon (last_cum_modEq hsat hpos)
    (hcanon.cells (t.rows.length - 1) Agg.IS_AGENT_CUMULATIVE_COL).1
    (hcanon.cells (t.rows.length - 1) Agg.IS_AGENT_CUMULATIVE_COL).2
    (by norm_num) (by norm_num)

/-- Last-row binding over ℤ: `n = pi[N_CELLS]` (both canonical). -/
theorem last_n (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) (hcanon : AggTraceCanon t) :
    nActiveAt t (t.rows.length - 1) = t.pub OuterPi.N_CELLS :=
  cellPub_eq hcanon (piLast_forces hsat hpos mem_lastNEqPi)

/-- **Booleanity of the `is_agent` column on EVERY row**: derived from the descriptor's own boolean
gate (+ primality + canonicality) on non-last rows; the envelope's last-row hypothesis elsewhere. -/
theorem isAgent_cases (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hcanon : AggTraceCanon t) :
    ∀ j, j < t.rows.length → isAgentAt t j = 0 ∨ isAgentAt t j = 1 := by
  intro j hj
  by_cases hnl : j + 1 = t.rows.length
  · have hje : j = t.rows.length - 1 := by omega
    rw [hje]; exact hcanon.lastAgentBool
  · have hm := mem_boolIsAgent
    rw [boolGate_eq] at hm
    have h := gate_forces hsat hj hnl hm
    simp only [EmittedExpr.eval] at h
    exact bool_of_boolGate h
      (hcanon.cells j (Agg.schCol Sched.IS_AGENT_CELL)).1
      (hcanon.cells j (Agg.schCol Sched.IS_AGENT_CELL)).2

/-- **Booleanity of the `consistent` column on EVERY row** (same derivation). -/
theorem consistent_cases (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hcanon : AggTraceCanon t) :
    ∀ j, j < t.rows.length → consistentAt t j = 0 ∨ consistentAt t j = 1 := by
  intro j hj
  by_cases hnl : j + 1 = t.rows.length
  · have hje : j = t.rows.length - 1 := by omega
    rw [hje]; exact hcanon.lastConsistentBool
  · have hm := mem_boolConsistent
    rw [boolGate_eq] at hm
    have h := gate_forces hsat hj hnl hm
    simp only [EmittedExpr.eval] at h
    exact bool_of_boolGate h
      (hcanon.cells j Agg.CONSISTENT_INDICATOR_COL).1
      (hcanon.cells j Agg.CONSISTENT_INDICATOR_COL).2

/-! ## §5 — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM). -/

/-- **`bilateralAgg_refines` — the Rung-1 functional-correctness refinement.**

A non-empty trace that SATISFIES the emitted `bilateralAggDescriptor` (via the deployed acceptance
predicate `Satisfied2`) IS a genuine bilateral-bundle aggregation `BundleAggregated t`: the bundle's
first and last cell carry the published turn identity, every non-final cell replays its schedule,
there is EXACTLY ONE agent cell across the bundle, and the published `n_cells` counts the consistent
cells. FIELD-FAITHFUL: the descriptor pins only `≡ [ZMOD p]`, so the bridge carries the explicit
canonicality envelope `AggTraceCanon` and the bundle-size bound `|rows| < p`; the two cumulative
facts are threaded from the row-0 seeds to the last-row boundaries by `running_sum_canon` (booleanity
of the contributions derived from the descriptor's own gates on non-last rows) — the genuine
aggregation content, EXACT over ℤ, no wrap-around forgery. No crypto carrier is consumed. -/
theorem bilateralAgg_refines
    (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t) (hne : t.rows ≠ [])
    (hcanon : AggTraceCanon t) (hsize : (t.rows.length : ℤ) < 2013265921) :
    BundleAggregated t := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  refine
    { nonempty := hpos
      turnHashFirst := fun i hi => ?_
      effectsFirst := fun i hi => ?_
      actorNonceFirst := ?_
      prevReceiptFirst := fun i hi => ?_
      turnHashLast := fun i hi => ?_
      effectsLast := fun i hi => ?_
      actorNonceLast := ?_
      prevReceiptLast := fun i hi => ?_
      replayCounts := fun i hii k hk => ?_
      replayRoots := fun i hii k hk => ?_
      exactlyOneAgent := ?_
      publishedCount := ?_ }
  · exact cellPub_eq hcanon (piFirst_forces hsat hpos (mem_A (mem_turn_hash .first i hi)))
  · exact cellPub_eq hcanon (piFirst_forces hsat hpos (mem_A (mem_turn_effects .first i hi)))
  · exact cellPub_eq hcanon (piFirst_forces hsat hpos (mem_A (mem_turn_nonce .first)))
  · exact cellPub_eq hcanon (piFirst_forces hsat hpos (mem_A (mem_turn_prev .first i hi)))
  · exact cellPub_eq hcanon (piLast_forces hsat hpos (mem_B (mem_turn_hash .last i hi)))
  · exact cellPub_eq hcanon (piLast_forces hsat hpos (mem_B (mem_turn_effects .last i hi)))
  · exact cellPub_eq hcanon (piLast_forces hsat hpos (mem_B (mem_turn_nonce .last)))
  · exact cellPub_eq hcanon (piLast_forces hsat hpos (mem_B (mem_turn_prev .last i hi)))
  · -- replayCounts on a non-final cell
    have hi : i < t.rows.length := by omega
    have hnl : i + 1 ≠ t.rows.length := by omega
    have h := gate_forces hsat hi hnl (mem_scheduleReplay_counts k hk)
    simp only [EmittedExpr.eval] at h
    exact cellCell_eq hcanon ((gate_modEq_iff (by ring)).mp h)
  · -- replayRoots on a non-final cell
    have hi : i < t.rows.length := by omega
    have hnl : i + 1 ≠ t.rows.length := by omega
    have h := gate_forces hsat hi hnl (mem_scheduleReplay_roots k hk)
    simp only [EmittedExpr.eval] at h
    exact cellCell_eq hcanon ((gate_modEq_iff (by ring)).mp h)
  · -- exactlyOneAgent: cum(last) = prefixSum is_agent (field recurrence + envelope), cum(last) = 1
    have key := running_sum_canon t.rows.length hsize (cumAt t) (isAgentAt t)
      (fun j => hcanon.cells j Agg.IS_AGENT_CUMULATIVE_COL)
      (isAgent_cases hsat hcanon)
      (seed_cum_modEq hsat hpos)
      (fun i hii => step_cum_modEq hsat i hii)
      (t.rows.length - 1) (by omega)
    rw [← key]; exact last_cum hsat hpos hcanon
  · -- publishedCount: n(last) = prefixSum consistent, and n(last) = pi[N_CELLS]
    have key := running_sum_canon t.rows.length hsize (nActiveAt t) (consistentAt t)
      (fun j => hcanon.cells j Agg.N_CELLS_ACTIVE_COL)
      (consistent_cases hsat hcanon)
      (seed_n_modEq hsat hpos)
      (fun i hii => step_n_modEq hsat i hii)
      (t.rows.length - 1) (by omega)
    rw [← key]; exact (last_n hsat hpos hcanon).symm

end Extract

/-! ## §6 — Non-vacuity: a concrete satisfying witness AND a concrete failing one. -/

/-- The abstract hash never enters this descriptor's denotation (no hash-sites / map-ops). -/
def hash0 : List ℤ → ℤ := fun _ => 0

theorem memOpsOf_agg : memOpsOf bilateralAggDescriptor = [] := rfl
theorem mapOpsOf_agg : mapOpsOf bilateralAggDescriptor = [] := rfl
theorem memLog_agg (t : VmTrace) : memLog bilateralAggDescriptor t = [] := by
  simp [memLog, memOpsOf_agg]
theorem mapLog_agg (t : VmTrace) : mapLog bilateralAggDescriptor t = [] := by
  simp [mapLog, mapOpsOf_agg]

/-- Cell 0: a NON-agent, consistent cell (`is_agent=0`, `cum=0`, `consistent=1`, `n=1`); turn-id /
counts / roots / expected columns all `0`. -/
def wr0 : Assignment := fun j => if j = 85 then 1 else if j = 86 then 1 else 0
/-- Cell 1 (the last cell): THE agent cell (`is_agent=1`, `cum=1`, `consistent=1`, `n=2`). -/
def wr1 : Assignment :=
  fun j => if j = 48 then 1 else if j = 84 then 1 else if j = 85 then 1 else if j = 86 then 2 else 0
/-- The public inputs: `pi[N_CELLS] = 2` (the two active cells); everything else `0`. -/
def wpub : Assignment := fun j => if j = 21 then 2 else 0
/-- The concrete 2-cell bundle: cell 0 (non-agent, consistent) · cell 1 (the agent cell). -/
def witTrace : VmTrace := { rows := [wr0, wr1], pub := wpub, tf := fun _ => [] }

/-- **The witness PROVABLY satisfies the emitted descriptor.** Every row constraint holds on both
cells (the CG-2 pins by value agreement; CG-3 replay by `0 = 0` on cell 0, vacuous on the last cell;
CG-4 booleans / padding / the two cumulative windows; the boundaries), and the memory legs are the
empty-log balance. -/
theorem witTrace_satisfies :
    Satisfied2 hash0 bilateralAggDescriptor (fun _ => 0) (fun _ => (0, 0)) [] witTrace where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    rw [show witTrace.rows.length = 2 from rfl]
    simp only [bilateralAggDescriptor] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [cg2PiBind, cg3Eq, colEqCol, boolGate_eq, paddingGate, cumAgentTransition,
        cumActiveTransition, firstCumSeed, firstNSeed, lastCumIsOne, lastNEqPi,
        VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        witTrace, envAt, wpub, EmittedExpr.eval, WindowExpr.eval,
        Nat.reduceAdd, Nat.reduceBEq, reduceIte, reduceCtorEq] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [bilateralAggDescriptor, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_agg]; simp
  memDisciplined := by rw [memLog_agg]; trivial
  memBalanced := by rw [memLog_agg]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_agg]; rfl
  mapTableFaithful := by rw [mapLog_agg]; rfl

/-- Every cell of `wr0` is a canonical BabyBear representative. -/
theorem wr0_canon (c : Nat) : 0 ≤ wr0 c ∧ wr0 c < 2013265921 := by
  unfold wr0; split_ifs <;> norm_num

/-- Every cell of `wr1` is a canonical BabyBear representative. -/
theorem wr1_canon (c : Nat) : 0 ≤ wr1 c ∧ wr1 c < 2013265921 := by
  unfold wr1; split_ifs <;> norm_num

/-- The zero row is canonical. -/
theorem zeroAsg_canon (c : Nat) : 0 ≤ zeroAsg c ∧ zeroAsg c < 2013265921 := by
  unfold zeroAsg; norm_num

/-- Row lookup on the 2-row witness: `wr0`, `wr1`, or the off-end zero row. -/
theorem witTrace_rowAt (i : Nat) :
    rowAt witTrace i = wr0 ∨ rowAt witTrace i = wr1 ∨ rowAt witTrace i = zeroAsg := by
  match i with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | _ + 2 => exact Or.inr (Or.inr rfl)

/-- **The witness INHABITS the canonicality envelope** — every cell / public input is canonical and
the last row's contribution columns are boolean, so `AggTraceCanon` is a real, concretely-satisfiable
hypothesis, not a vacuous guard. -/
theorem witTrace_canon : AggTraceCanon witTrace where
  cells := by
    intro i c
    rcases witTrace_rowAt i with h | h | h <;> rw [h]
    exacts [wr0_canon c, wr1_canon c, zeroAsg_canon c]
  pubs := by
    intro k
    show 0 ≤ wpub k ∧ wpub k < 2013265921
    unfold wpub; split_ifs <;> norm_num
  lastAgentBool := by right; decide
  lastConsistentBool := by right; decide

/-- **The bridge FIRES on the witness** (the SAT hypothesis is genuinely inhabited): the concrete
2-cell bundle is a `BundleAggregated`. -/
theorem witness_aggregated : BundleAggregated witTrace :=
  bilateralAgg_refines witTrace_satisfies (by decide) witTrace_canon (by decide)

/-- The recovered aggregation is CONCRETE and non-trivial: exactly ONE agent cell
(`is_agent 0 + is_agent 1 = 0 + 1 = 1`), and the published count is `2` = the two consistent cells
(`1 + 1`). The two cumulative recurrences and the schedule replay on cell 0 were all exercised. -/
theorem witness_value :
    prefixSum (isAgentAt witTrace) (witTrace.rows.length - 1) = 1 ∧
    witTrace.pub OuterPi.N_CELLS = 2 ∧
    prefixSum (consistentAt witTrace) (witTrace.rows.length - 1) = 2 := by
  refine ⟨witness_aggregated.exactlyOneAgent, by decide, ?_⟩
  exact witness_aggregated.publishedCount.symm.trans (by decide)

/-- A WRONG bundle: a single cell whose `is_agent_cumulative` is `0`, not the required `1`. -/
def badTrace : VmTrace := { rows := [zeroAsg], pub := zeroAsg, tf := fun _ => [] }

/-- **A WRONG bundle PROVABLY fails the hypothesis** (the constraint bites — the Satisfied2 accept-set
does NOT contain this trace): the single-agent boundary `lastCumIsOne` forces the last-row cumulative
`≡ 1 [ZMOD p]`, but `badTrace` carries `0` and `p ∤ 1` — the FIELD gate itself rejects, with no
canonicality needed. -/
theorem badTrace_not_satisfied :
    ¬ Satisfied2 hash0 bilateralAggDescriptor (fun _ => 0) (fun _ => (0, 0)) [] badTrace := by
  intro h
  have hm := last_cum_modEq h (by decide)
  have h0 : cumAt badTrace (badTrace.rows.length - 1) = 0 := rfl
  rw [h0] at hm
  obtain ⟨k, hk⟩ := hm.dvd
  omega

/-! ## §7 — Axiom tripwires. -/

#assert_axioms bilateralAgg_refines
#assert_axioms witTrace_satisfies
#assert_axioms witness_aggregated
#assert_axioms witness_value
#assert_axioms badTrace_not_satisfied

end Dregg2.Circuit.Emit.BilateralAggregationRefine
