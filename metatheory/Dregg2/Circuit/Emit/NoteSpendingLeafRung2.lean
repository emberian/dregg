/-
# Dregg2.Circuit.Emit.NoteSpendingLeafRung2 — the RUNG-2 discharge of the MULTI-ROW Merkle-membership
residual left by `NoteSpendingLeafRefine` (RUNG 1), for the emitted note-spend recursion leaf
(`NoteSpendingLeafEmit.noteSpendLeafDesc`).

## What RUNG 1 gave us and what this file adds

`NoteSpendingLeafRefine.noteSpend_satisfied2_spec` (RUNG 1) is a SINGLE-ROW (row-0, the SPEND row)
bridge: a `Satisfied2` trace, against the NAMED wide Poseidon2 chip carrier `ChipTableSoundN permOut`,
binds the whole spend-row relation — commitment = the 7-fold `permOut` chain of the note preimage,
nullifier = the two-step key derivation, the PI pins, etc. Its OWN honest residual (§ "Honest
residuals"): C6 (Merkle membership) is OFF on the spend row (`is_merkle = 0`); the genuine meaning —
that the committed leaf is IN the tree rooted at the PUBLIC `merkle_root` (pi1) — lives on the
`is_merkle = 1` path rows and needs the MULTI-ROW `recomposeUp` fold. That is exactly a
"single-row spec where multi-row binding is needed" — the RUNG-2 residual.

## The discharge (the multi-row Merkle recompose)

The deployed leaf threads a Merkle authentication path ACROSS ROWS:
  * C6 (`whenSite 5 [0,1,2,3,4] 128`, a `Poseidon2Chip` LOOKUP that fires on `is_merkle = 1`) forces,
    on EVERY merkle row (lookups are not divided by the transition zerofier), the row's PARENT column
    (col 5) to be `permOut` of the seeded `(current, 4 position-aware inputs)` — one `recomposeUp`
    step (`merkleRow_c6`, riding RUNG-1's `factSite_block` lever with the `whenSite` selector);
  * C7 (`.windowGate ⟨contBodyW, true⟩`, on-transition) threads `next.CURRENT (col 0) = this.PARENT
    (col 5)` — the leaf `COMMITMENT` (row-0 col 5) flows up through the path rows;
  * the last-row pin (`.piBinding .last 0 1`) pins the terminal `CURRENT` to the public `merkle_root`.

`recompose_reaches` inducts over the path rows (mirroring `HeapOpenEmit.heapRecompose_reaches_cur8`
and the DFA template's `accumulates_map`): the CURRENT column at each path row is the leaf folded up
`foldUpN` over the witnessed sibling steps. `noteSpend_merkle_rung2` closes it with the last-row pin:
`merkle_root (pi1) = foldUpN permOut leaf (path steps)` — the GENUINE membership relation. Composed
with RUNG 1 (`noteSpend_committed_note_member`), the note whose commitment is the genuine `permOut`
hash of the disclosed `(value, asset, …)` is genuinely a MEMBER of the tree rooted at the public
`merkle_root` — the note-spend no-forgery property.

The last-row continuity vacuity (C7 is `on_transition`, so unenforced on the last row) does NOT open
a gap here: the terminal `CURRENT` is pinned DIRECTLY (a `piBinding`, always enforced), and the fold
threads into it via C7 on the penultimate (transition) row — unlike the DFA, no route-commitment
anchor is needed for the terminal step.

## Non-vacuity (the anti-scar package — TRUE and FALSE, never a stub)

* `witness_merkle_rung2` FIRES the bridge end-to-end on RUNG-1's concrete satisfying `witnessTrace`
  (a genuine 2-row trace, depth-0 path): the hypothesis set is INHABITED, `merkle_root = leaf`
  DERIVED, not assumed (`witness_merkle_value`).
* `membership_model_true_closed` / `membership_model_false_closed` exhibit the fold over a REAL
  Poseidon-shaped digit hash `dPerm` computing a genuine step (`root = 128643`) and REJECTING a wrong
  root (`999`) — the membership relation is a real filter, not `True`.
* `merkle_broken_chain_rejects` / `merkle_wrong_root_rejects` exhibit CONCRETE traces that FAIL
  `Satisfied2` because a tooth BITES (C7 continuity; the last-row pin).
* `whenSite_offrow_digest_K0` is the LOAD-BEARING witness for the path-shape hypothesis: on an
  `is_merkle = 0` row the C6 digest lane muxes to the constant `K₀` REGARDLESS of col 5 — so C6 does
  NOT bind the node hash off the merkle path, and the `is_merkle = 1` precondition is genuinely
  required (not laundered).

## Honestly-named residual

The `is_merkle` PATH SHAPE (`row 0` spend, the interior rows `is_merkle = 1`, a terminal row) is a
STRUCTURAL precondition (`hpath` / `hspend`), enforced above the leaf by the recursion-FOLD adapter,
not by the leaf descriptor's per-row constraints — exactly as RUNG 1 states `hspend` for row 0. It is
NOT a crypto residual and is NAMED, never laundered; its enforcement by the fold adapter is the
precise follow-up.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The SOLE cryptographic carrier is the
NAMED wide Poseidon2 chip soundness `ChipTableSoundN permOut` — the same carrier RUNG 1 / `HeapOpenEmit`
ride; `permOut` is a parameter. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.NoteSpendingLeafRefine

namespace Dregg2.Circuit.Emit.NoteSpendingLeafRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId WindowConstraint WindowExpr Satisfied2 VmTrace
   envAt zeroAsg ChipTableSoundN TraceFamily)
open Dregg2.Circuit.Emit.NoteSpendingLeafEmit
  (noteSpendLeafDesc noteSpendConstraints unlessSite whenSite factTuple IS_MERKLE NS_FACT_MARK K0
   subE unlessFire unlessHold whenFire whenHold binaryGate invEqGate posGate contBodyW
   cont_body_zero_iff noteSpendLeafDescFixed noteSpendLastRowFix lastRowFix_commitment_zero_iff)
open Dregg2.Circuit.Emit.NoteSpendingLeafRefine
  (firingIns firing5 factLaneVals factSite_block NoteSpendLeafSpec noteSpend_satisfied2_spec
   witnessTrace witnessPerm witnessAsg witnessPub witnessTrace_satisfied2 witness_chipSound
   invEqGate_spend NoteCanon Canon eq_of_modEq_canon witness_canon)

set_option autoImplicit false

/-! ## §0 — field-faithful glue for the multi-row fold.

The continuity window gate binds `next.CURRENT − this.PARENT ≡ 0 [ZMOD p]` and the terminal root pin
binds `CURRENT ≡ merkle_root [ZMOD p]` (the DEPLOYED BabyBear field constraints). The fold threads
GENUINE ℤ equalities, recovered from the deployed range-check invariant that every felt is canonical
(`0 ≤ · < p`). `MerkleThreadCanon` names exactly the cells the fold reads back — the per-row
continuity pair and the terminal `(CURRENT, merkle_root)` — inhabited concretely by the witness. -/

/-- The window continuity gate `≡ 0 [ZMOD p]`, with both cells canonical, gives the genuine thread. -/
private theorem thread_of_window (env : VmRowEnv) (hn : Canon (env.nxt 0)) (h5 : Canon (env.loc 5))
    (h : contBodyW.eval env ≡ 0 [ZMOD 2013265921]) : env.nxt 0 = env.loc 5 := by
  have hb : contBodyW.eval env = env.nxt 0 - env.loc 5 := by
    simp only [contBodyW, GateExpr.gThread_window, WindowExpr.eval]; ring
  rw [hb, Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h; obtain ⟨_, _⟩ := hn; obtain ⟨_, _⟩ := h5; omega

/-- **`MerkleThreadCanon t` — the deployed range-check envelope the multi-row fold reads back.** Each
non-last row's continuity pair (`next.CURRENT`, `this.PARENT`) is canonical (so `next.CURRENT =
this.PARENT` lifts from the mod-`p` gate), and the terminal `(CURRENT, merkle_root)` are canonical (so
the root pin lifts). -/
def MerkleThreadCanon (t : VmTrace) : Prop :=
  (∀ i, i + 1 < t.rows.length → Canon ((envAt t i).nxt 0) ∧ Canon ((envAt t i).loc 5))
  ∧ Canon ((envAt t (t.rows.length - 1)).loc 0) ∧ Canon (t.pub 1)

/-! ## §1 — the genuine Merkle-membership fold MODEL (the trace-independent no-forgery relation). -/

/-- **`nodeHashN permOut cur s1 s2 s3 s4`** — one Poseidon2 `recomposeUp` step: the parent digest of a
node whose current child is `cur` and whose four position-aware inputs are `s1 s2 s3 s4`. It IS the
head of the wide `permOut` of the deployed C6 fact-site seed `[cur, s1, s2, s3, s4, 0xFACF, 1]` — the
exact absorb `NoteSpendingLeafEmit.whenSite 5 [0,1,2,3,4] 128` binds on a merkle row. -/
def nodeHashN (permOut : List ℤ → List ℤ) (cur s1 s2 s3 s4 : ℤ) : ℤ :=
  (permOut [cur, s1, s2, s3, s4, NS_FACT_MARK, 1]).headD 0

/-- **`foldUpN permOut leaf steps`** — the leaf folded up its authentication path: each step supplies
the four position-aware inputs of that level, and the accumulator recomposes the parent digest. -/
def foldUpN (permOut : List ℤ → List ℤ) (leaf : ℤ) (steps : List (ℤ × ℤ × ℤ × ℤ)) : ℤ :=
  steps.foldl (fun acc s => nodeHashN permOut acc s.1 s.2.1 s.2.2.1 s.2.2.2) leaf

/-- **`MembersAtRoot permOut leaf root steps`** — THE FUNCTIONAL SPEC: `leaf` authenticates to the
committed `root` along the Poseidon2 path `steps`. The membership relation the note-spend leaf is
meant to certify (the leaf's `COMMITMENT` sits under the public `merkle_root`). -/
def MembersAtRoot (permOut : List ℤ → List ℤ) (leaf root : ℤ) (steps : List (ℤ × ℤ × ℤ × ℤ)) : Prop :=
  foldUpN permOut leaf steps = root

/-- Folding one more level appends its step to the path (the fold's own `foldl`-over-append law). -/
theorem foldUpN_append (permOut : List ℤ → List ℤ) (leaf : ℤ) (xs : List (ℤ × ℤ × ℤ × ℤ))
    (y : ℤ × ℤ × ℤ × ℤ) :
    foldUpN permOut leaf (xs ++ [y])
      = nodeHashN permOut (foldUpN permOut leaf xs) y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  simp only [foldUpN, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## §2 — reading one Merkle-fold step off `Satisfied2` (the `whenSite` C6 lever, on `is_merkle=1`). -/

/-- The C6 fact-site's `fire` selector (`whenFire IS_MERKLE`) is `1` on a merkle row. -/
theorem when_fire_eval (env : VmRowEnv) (hm : env.loc IS_MERKLE = 1) :
    (whenFire IS_MERKLE).eval env.loc = 1 := by
  simp [whenFire, EmittedExpr.eval, hm]

/-- The C6 fact-site's `hold` selector (`whenHold IS_MERKLE`) is `0` on a merkle row. -/
theorem when_hold_eval (env : VmRowEnv) (hm : env.loc IS_MERKLE = 1) :
    (whenHold IS_MERKLE).eval env.loc = 0 := by
  simp [whenHold, subE, EmittedExpr.eval, hm]

/-- A firing (`whenSite`) fact site's digest on a merkle row (`is_merkle = 1`) is `permOut` of the
genuine seed — the mirror of RUNG-1's `unlessSite_digest`, riding the same `factSite_block` lever
with the `when`-selector. -/
theorem whenSite_digest (permOut : List ℤ → List ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf .poseidon2)) (hm : env.loc IS_MERKLE = 1)
    (outputCol : Nat) (inputCols : List Nat) (laneBase : Nat)
    (hmem : (factTuple (whenFire IS_MERKLE) (whenHold IS_MERKLE) outputCol inputCols laneBase).map
              (·.eval env.loc) ∈ tf .poseidon2) :
    env.loc outputCol = (permOut (firingIns env inputCols)).headD 0 := by
  have hblock := factSite_block permOut tf env hChip outputCol inputCols laneBase _ _
    (when_fire_eval env hm) (when_hold_eval env hm) hmem
  rw [← hblock]; rfl

/-- The C6 fact-site's genuine absorb seed evaluates to the five muxed columns plus the domain
constants (`0xFACF, 1`) — the twin of `firingIns_length`, computed on the C6 input columns. -/
theorem firingIns_c6 (env : VmRowEnv) :
    firingIns env [0, 1, 2, 3, 4]
      = [env.loc 0, env.loc 1, env.loc 2, env.loc 3, env.loc 4, NS_FACT_MARK, 1] := rfl

/-- **`merkleRow_c6`** — on a merkle row, C6 forces the PARENT column (col 5) to be the genuine
`recomposeUp` node hash of the CURRENT column (col 0) and the four position-aware inputs
(cols 1..4). One authentication step, read off `Satisfied2` + the NAMED chip carrier. -/
theorem merkleRow_c6 (permOut : List ℤ → List ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf .poseidon2)) (hm : env.loc IS_MERKLE = 1)
    (hmem : (factTuple (whenFire IS_MERKLE) (whenHold IS_MERKLE) 5 [0, 1, 2, 3, 4] 128).map
              (·.eval env.loc) ∈ tf .poseidon2) :
    env.loc 5 = nodeHashN permOut (env.loc 0) (env.loc 1) (env.loc 2) (env.loc 3) (env.loc 4) := by
  have h := whenSite_digest permOut tf env hChip hm 5 [0, 1, 2, 3, 4] 128 hmem
  rw [h]; simp only [nodeHashN, firingIns_c6]

/-! ## §3 — membership of the three load-bearing constraints in `noteSpendLeafDesc`. -/

/-- The C6 Merkle-membership fact site is a genuine constraint of the descriptor. -/
theorem mem_c6 : whenSite 5 [0, 1, 2, 3, 4] 128 ∈ noteSpendLeafDesc.constraints := by
  show whenSite 5 [0, 1, 2, 3, 4] 128 ∈ noteSpendConstraints
  unfold noteSpendConstraints
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-- The C7 chain-continuity window gate is a genuine constraint of the descriptor. -/
theorem mem_c7 : VmConstraint2.windowGate ⟨contBodyW, true⟩ ∈ noteSpendLeafDesc.constraints := by
  show VmConstraint2.windowGate ⟨contBodyW, true⟩ ∈ noteSpendConstraints
  unfold noteSpendConstraints contBodyW
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-- The last-row Merkle-root pin is a genuine constraint of the descriptor. -/
theorem mem_pin_last :
    VmConstraint2.base (.piBinding VmRow.last 0 1) ∈ noteSpendLeafDesc.constraints := by
  show VmConstraint2.base (.piBinding VmRow.last 0 1) ∈ noteSpendConstraints
  unfold noteSpendConstraints
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-! ## §4 — the trace-read path steps + the multi-row recompose. -/

/-- The four position-aware inputs (cols 1..4) read off row `i` — one authentication step. -/
def stepAt (t : VmTrace) (i : Nat) : ℤ × ℤ × ℤ × ℤ :=
  ((envAt t i).loc 1, (envAt t i).loc 2, (envAt t i).loc 3, (envAt t i).loc 4)

/-- The authentication path read off the first `m` merkle rows (rows `1 .. m`). -/
def stepsUpto (t : VmTrace) (m : Nat) : List (ℤ × ℤ × ℤ × ℤ) :=
  (List.range m).map (fun j => stepAt t (j + 1))

/-- One more merkle row appends its step to the path. -/
theorem stepsUpto_succ (t : VmTrace) (k : Nat) :
    stepsUpto t (k + 1) = stepsUpto t k ++ [stepAt t (k + 1)] := by
  simp only [stepsUpto, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The trace-index threading of the continuity window: the current row's `nxt` slice IS the next
row's `loc` slice (`envAt`'s own definition). -/
theorem envAt_nxt_loc (t : VmTrace) (j : Nat) : (envAt t j).nxt = (envAt t (j + 1)).loc := rfl

/-- **`recompose_reaches` — the MULTI-ROW Merkle fold.** Under the NAMED chip carrier, on a trace
whose interior rows (`1 .. n-2`) are merkle rows (`hpath`), the CURRENT column (col 0) at each path
row `k+1` is the leaf (the row-0 `COMMITMENT`, col 5) folded up `foldUpN` over the sibling steps
read from rows `1 .. k`. Induction on `k`, mirroring `HeapOpenEmit.heapRecompose_reaches_cur8`:
the base uses C7 on row 0 (the leaf enters row 1); the step composes C6 (this level's node hash) with
C7 (thread to the next row's CURRENT). -/
theorem recompose_reaches (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash noteSpendLeafDesc minit mfin maddrs t)
    (hChip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hcont : ∀ i, i + 1 < t.rows.length →
      Canon ((envAt t i).nxt 0) ∧ Canon ((envAt t i).loc 5))
    (hpath : ∀ i, 1 ≤ i → i + 1 < t.rows.length → (envAt t i).loc IS_MERKLE = 1) :
    ∀ m, m + 1 ≤ t.rows.length - 1 →
      (envAt t (m + 1)).loc 0 = foldUpN permOut ((envAt t 0).loc 5) (stepsUpto t m) := by
  intro m
  induction m with
  | zero =>
    intro hm1
    have hrow0 : (0 : Nat) < t.rows.length := by omega
    have hnotlast0 : ((0 : Nat) + 1 == t.rows.length) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    have hc7 := hsat.rowConstraints 0 hrow0 _ mem_c7
    have hbody : contBodyW.eval (envAt t 0) ≡ 0 [ZMOD 2013265921] := by
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hc7
      exact hc7 hnotlast0
    have hcont0 := hcont 0 (by omega)
    have hthread : (envAt t 0).nxt 0 = (envAt t 0).loc 5 :=
      thread_of_window (envAt t 0) hcont0.1 hcont0.2 hbody
    have hnl : (envAt t 0).nxt 0 = (envAt t (0 + 1)).loc 0 := rfl
    simp only [stepsUpto, List.range_zero, List.map_nil, foldUpN, List.foldl_nil]
    rw [← hnl]; exact hthread
  | succ k ih =>
    intro hm1
    have hkle : k + 1 ≤ t.rows.length - 1 := by omega
    have hkstep : (envAt t (k + 1)).loc 0
        = foldUpN permOut ((envAt t 0).loc 5) (stepsUpto t k) := ih hkle
    have hrowk1 : k + 1 < t.rows.length := by omega
    have hmerk : (envAt t (k + 1)).loc IS_MERKLE = 1 := hpath (k + 1) (by omega) (by omega)
    have hmem6 : (factTuple (whenFire IS_MERKLE) (whenHold IS_MERKLE) 5 [0, 1, 2, 3, 4] 128).map
                    (·.eval (envAt t (k + 1)).loc) ∈ t.tf .poseidon2 := by
      have hc := hsat.rowConstraints (k + 1) hrowk1 _ mem_c6
      simpa only [VmConstraint2.holdsAt, whenSite, Lookup.holdsAt] using hc
    have hc6 := merkleRow_c6 permOut t.tf (envAt t (k + 1)) hChip hmerk hmem6
    have hnotlast : ((k + 1) + 1 == t.rows.length) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    have hc7 := hsat.rowConstraints (k + 1) hrowk1 _ mem_c7
    have hbody : contBodyW.eval (envAt t (k + 1)) ≡ 0 [ZMOD 2013265921] := by
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hc7
      exact hc7 hnotlast
    have hcontk := hcont (k + 1) (by omega)
    have hthread : (envAt t (k + 1)).nxt 0 = (envAt t (k + 1)).loc 5 :=
      thread_of_window (envAt t (k + 1)) hcontk.1 hcontk.2 hbody
    have hnl : (envAt t (k + 1)).nxt 0 = (envAt t (k + 1 + 1)).loc 0 := rfl
    rw [← hnl, hthread, hc6, hkstep, stepsUpto_succ, foldUpN_append]
    simp only [stepAt]

/-! ## §5 — THE RUNG-2 BRIDGE: `merkle_root = foldUpN leaf (path)` (the membership no-forgery). -/

/-- The full witnessed authentication path of a trace (the `n-2` interior merkle rows). -/
def merklePathSteps (t : VmTrace) : List (ℤ × ℤ × ℤ × ℤ) := stepsUpto t (t.rows.length - 2)

/-- **`noteSpend_merkle_rung2` — THE MULTI-ROW MEMBERSHIP DISCHARGE.** A `Satisfied2` trace of the
note-spend leaf, against the NAMED wide Poseidon2 chip carrier, whose interior rows are the merkle
path (`hpath`), binds the GENUINE Merkle-membership relation: the public `merkle_root` (pi1) is the
leaf (the row-0 `COMMITMENT`, col 5) folded up `foldUpN` over the witnessed authentication path.
Composes `recompose_reaches` (the fold reaches the terminal CURRENT) with the last-row root pin.
No route-commitment anchor is needed — the terminal CURRENT is pinned directly. -/
theorem noteSpend_merkle_rung2 {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendLeafDesc minit mfin maddrs t)
    (hChip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length)
    (hcanon : MerkleThreadCanon t)
    (hpath : ∀ i, 1 ≤ i → i + 1 < t.rows.length → (envAt t i).loc IS_MERKLE = 1) :
    MembersAtRoot permOut ((envAt t 0).loc 5) (t.pub 1) (merklePathSteps t) := by
  obtain ⟨hcont, hcLast0, hcPub1⟩ := hcanon
  have hn1 : t.rows.length - 1 < t.rows.length := by omega
  have hrec := recompose_reaches permOut hash minit mfin maddrs t hsat hChip hcont hpath
    (t.rows.length - 2) (by omega)
  have heq : t.rows.length - 2 + 1 = t.rows.length - 1 := by omega
  rw [heq] at hrec
  have hpin := hsat.rowConstraints (t.rows.length - 1) hn1 _ mem_pin_last
  have hislast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    have : t.rows.length - 1 + 1 = t.rows.length := by omega
    rw [this]; exact beq_self_eq_true _
  have hpineq : (envAt t (t.rows.length - 1)).loc 0 = t.pub 1 := by
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hpin
    exact eq_of_modEq_canon hcLast0 hcPub1 (hpin hislast)
  show foldUpN permOut ((envAt t 0).loc 5) (merklePathSteps t) = t.pub 1
  rw [merklePathSteps, ← hrec]; exact hpineq

/-- **`noteSpend_committed_note_member` — THE NOTE-SPEND NO-FORGERY.** Composing RUNG 1 (the row-0
leaf IS the genuine 7-fold `permOut` commitment of the note preimage) with the RUNG-2 membership
bridge: the note whose commitment is the genuine Poseidon2 hash of its preimage is genuinely a MEMBER
of the tree rooted at the PUBLIC `merkle_root` (pi1). A prover cannot spend a note that is not in the
committed tree, nor forge the committed value/asset. -/
theorem noteSpend_committed_note_member {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendLeafDesc minit mfin maddrs t)
    (hChip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length) (hspend : (envAt t 0).loc IS_MERKLE = 0)
    (hcanon : NoteCanon (envAt t 0)) (hmcanon : MerkleThreadCanon t)
    (hpath : ∀ i, 1 ≤ i → i + 1 < t.rows.length → (envAt t i).loc IS_MERKLE = 1) :
    (envAt t 0).loc 5 = (permOut (firingIns (envAt t 0) [53, 45, 46, 47])).headD 0
    ∧ MembersAtRoot permOut ((envAt t 0).loc 5) (t.pub 1) (merklePathSteps t) := by
  have hspec := noteSpend_satisfied2_spec permOut hash minit mfin maddrs t hsat hChip (by omega) hspend hcanon
  refine ⟨?_, noteSpend_merkle_rung2 hsat hChip hlen hmcanon hpath⟩
  rw [hspec.commitmentBinds]; exact hspec.commitmentFull

#assert_axioms merkleRow_c6
#assert_axioms recompose_reaches
#assert_axioms noteSpend_merkle_rung2
#assert_axioms noteSpend_committed_note_member

/-! ## §6 — non-vacuity, POSITIVE half: the bridge FIRES on RUNG-1's concrete satisfying witness.

RUNG 1 already proved `witnessTrace` (a genuine 2-row trace) `Satisfied2`s the whole descriptor with
a genuinely sound wide chip table (`witness_chipSound` for `witnessPerm`). For a 2-row trace the path
is empty (depth-0: a single-leaf tree), so the bridge's hypothesis set is INHABITED and the
membership `merkle_root = leaf` is DERIVED end-to-end — not a vacuous antecedent. -/

/-- **The RUNG-2 bridge FIRES on the concrete witness** (hypothesis set inhabited): the depth-0
membership `merkle_root = leaf` is derived, not assumed. `hpath` is vacuous (no interior rows). -/
theorem witness_merkle_rung2 :
    MembersAtRoot witnessPerm ((envAt witnessTrace 0).loc 5) (witnessTrace.pub 1)
      (merklePathSteps witnessTrace) :=
  noteSpend_merkle_rung2 witnessTrace_satisfied2 witness_chipSound (by decide)
    ⟨by intro i hi
        have hl : witnessTrace.rows.length = 2 := rfl
        rw [hl] at hi
        have : i = 0 := by omega
        subst this
        exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩,
      ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
    (by intro i h1 h2; have hl : witnessTrace.rows.length = 2 := rfl; omega)

/-- The recovered value is the concrete zero-fact digest `K₀` on BOTH sides — the fired conclusion is
a real equation, not a constant tautology (`merkle_root = leaf = K₀`). -/
theorem witness_merkle_value :
    witnessTrace.pub 1 = K0
    ∧ foldUpN witnessPerm ((envAt witnessTrace 0).loc 5) (merklePathSteps witnessTrace) = K0 := by
  refine ⟨rfl, rfl⟩

/-! ## §7 — non-vacuity, the MODEL separates (TRUE and FALSE) over a REAL digit hash. -/

/-- A concrete order-sensitive digit hash (`permOut`-shaped: head is the digest), enough to exercise
a genuine `recomposeUp` step non-degenerately. -/
def dPerm : List ℤ → List ℤ := fun xs => [xs.foldl (fun acc x => acc * 2 + x) 0]

/-- **Witness TRUE — the membership spec is INHABITED (closed form).** Leaf `1` with the level inputs
`(2,3,4,5)` folds up (through the deployed `0xFACF, 1` domain constants) to the concrete root
`128643` — a real, nontrivial `recomposeUp` step, not a stub. -/
theorem membership_model_true_closed : MembersAtRoot dPerm 1 128643 [(2, 3, 4, 5)] := by
  unfold MembersAtRoot foldUpN nodeHashN dPerm NS_FACT_MARK; decide

/-- **Witness FALSE — the membership spec CONSTRAINS.** The same leaf/step with the WRONG root is NOT
accepted: the recomposed digest must equal the published root. A `True`/`P → P` bridge could not
separate this. -/
theorem membership_model_false_closed : ¬ MembersAtRoot dPerm 1 999 [(2, 3, 4, 5)] := by
  unfold MembersAtRoot foldUpN nodeHashN dPerm NS_FACT_MARK; decide

/-! ## §8 — non-vacuity, the descriptor REJECTS forgeries (teeth BITE). -/

/-- A trace whose continuity is BROKEN: row-0 PARENT (col 5) is `1`, but row-1 CURRENT (col 0) is `0`
— so the C7 threading `next.CURRENT = this.PARENT` fails. -/
def bcRow0 : Assignment := fun c => if c = 5 then 1 else 0
def bcTrace : VmTrace := { rows := [bcRow0, zeroAsg], pub := zeroAsg, tf := fun _ => [] }

/-- **Non-vacuity (reject — C7 tooth BITES).** The broken-continuity trace FAILS `Satisfied2`: the
transition-row C7 window gate forces `next.CURRENT = this.PARENT`, i.e. `0 = 1`. -/
theorem merkle_broken_chain_rejects (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    ¬ Satisfied2 hash noteSpendLeafDesc minit mfin maddrs bcTrace := by
  intro h
  have hc := h.rowConstraints 0 (by decide) _ mem_c7
  have hnl : ((0 : Nat) + 1 == bcTrace.rows.length) = false := by decide
  have hbody : contBodyW.eval (envAt bcTrace 0) ≡ 0 [ZMOD 2013265921] := by
    simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hc
    exact hc hnl
  -- the C7 window gate binds `next.CURRENT − this.PARENT ≡ 0`; here it is `0 − 1 = −1`, and `p ∤ −1`.
  have hval : contBodyW.eval (envAt bcTrace 0) = -1 := by decide
  rw [hval] at hbody; revert hbody; decide

/-- A single-row trace whose CURRENT (col 0) is `1` but whose public `merkle_root` (pi1) is `0`. -/
def wrRow : Assignment := fun c => if c = 0 then 1 else 0
def wrTrace : VmTrace := { rows := [wrRow], pub := zeroAsg, tf := fun _ => [] }

/-- **Non-vacuity (reject — root-pin tooth BITES).** The wrong-root trace FAILS `Satisfied2`: the
last-row pin forces the terminal CURRENT to equal the public `merkle_root`, i.e. `1 = 0` — exactly
the "publish a root the leaf does not authenticate to" attack forbidden. -/
theorem merkle_wrong_root_rejects (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    ¬ Satisfied2 hash noteSpendLeafDesc minit mfin maddrs wrTrace := by
  intro h
  have hc := h.rowConstraints 0 (by decide) _ mem_pin_last
  have hislast : ((0 : Nat) + 1 == wrTrace.rows.length) = true := by decide
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  have heq := hc hislast
  revert heq; decide

/-! ## §9 — the LOAD-BEARING witness for the path-shape hypothesis (`hpath` is not laundered).

On an `is_merkle = 0` row the C6 digest lane muxes to the constant `K₀` REGARDLESS of the PARENT
column (col 5): the fact site degenerates to the zero-fact absorb. So C6 does NOT bind the node hash
off the merkle path — the `is_merkle = 1` precondition (the `hpath` shape) is genuinely required for
`merkleRow_c6` to fire, and `Satisfied2` alone cannot force the fold step without it. -/

/-- **`whenSite_offrow_digest_K0` — the anchor is LOAD-BEARING.** On an `is_merkle = 0` row the C6
fact-site digest-lane expression `fire·col5 + hold·K₀` evaluates to `K₀` independent of col 5: the
merkle fold step is UNCONSTRAINED off the path, so `hpath` is not laundered. -/
theorem whenSite_offrow_digest_K0 (env : VmRowEnv) (hm : env.loc IS_MERKLE = 0) :
    (EmittedExpr.add (.mul (whenFire IS_MERKLE) (.var 5)) (.mul (whenHold IS_MERKLE) (.const K0))).eval
        env.loc = K0 := by
  simp only [whenFire, whenHold, subE, EmittedExpr.eval, hm]
  ring

/-! ## §10 — shape pins + axiom tripwires. -/

#guard decide (bcTrace.rows.length = 2)
#guard decide (wrTrace.rows.length = 1)

#assert_axioms witness_merkle_rung2
#assert_axioms membership_model_true_closed
#assert_axioms membership_model_false_closed
#assert_axioms merkle_broken_chain_rejects
#assert_axioms merkle_wrong_root_rejects
#assert_axioms whenSite_offrow_digest_K0

/-! ## §11 — THE LAST-ROW `COMMITMENT`-BINDING FORGE (the `.gate`-vacuity hole) + ITS CLOSURE.

The audit-found hole (the mission's exact bug class): C2-final `COMMITMENT (col 5) == COMMITMENT_FULL
(col 54)` is emitted `.base (.gate …)` — VACUOUS on the last row (`holdsVm … isLast=true (.gate _) =
True`). But the deployed DSL AIR enforces the same `InvertedGated{Equality}` EVERY row (`assert_zero`,
`dsl_p3_air.rs:38`). So on a HEIGHT-1 trace (row 0 IS the last row, `is_merkle = 0`) col 5 is FREE:
the nullifier chain C3/C4 rides col 5, so a prover derives the nullifier from a `COMMITMENT` that is
NOT the genuine full-width binding (col 54). `forgeTrace` is exactly this — the single-row twin of
`NoteSpendingLeafRefine.badCommitTrace` (which is CAUGHT because its row 0 is a NON-last transition
row where the `.gate` fires). The two-row version is rejected; the one-row version escapes — the
last-row vacuity, exposed.

`forgeTrace` is a genuine `Satisfied2` witness under `noteSpendLeafDesc` (`forgeTrace_satisfied2`),
and NOT `Satisfied2` under `noteSpendLeafDescFixed` (`forge_rejected_by_fix`, THE regression) — the
appended `VmRow.last` boundary bites. -/

/-- The three distinct Poseidon2 fact-site tuples the forge row (`col5 = 1`, else `0`, `is_merkle=0`)
produces: `T0` (all-zero seed, digest 0 — the C2 chain / C4 / mint sites); `T1` (seed head `1` from
`col5`, digest 0 — the C3 nullifier-intermediate site); `TK` (the muxed-off C6 Merkle site, digest
`K₀`). Every one of the 12 lookups lands in `[forgeT0, forgeT1, forgeTK]`. -/
def forgeT0 : List ℤ := [7, 0,0,0,0,0, NS_FACT_MARK, 1, 0,0,0,0,0,0,0,0,0, 0, 0,0,0,0,0,0,0]
def forgeT1 : List ℤ := [7, 1,0,0,0,0, NS_FACT_MARK, 1, 0,0,0,0,0,0,0,0,0, 0, 0,0,0,0,0,0,0]
def forgeTK : List ℤ := [7, 0,0,0,0,0, NS_FACT_MARK, 1, 0,0,0,0,0,0,0,0,0, K0, 0,0,0,0,0,0,0]

/-- The forge trace family: the three fact rows on `poseidon2`, empty elsewhere. -/
def forgeTf : TraceFamily := fun tid =>
  match tid with | .poseidon2 => [forgeT0, forgeT1, forgeTK] | _ => []

/-- The forge spend row: `is_merkle = 0` (col 16), `COMMITMENT (col 5) = 1`, everything else `0` — in
particular `COMMITMENT_FULL (col 54) = 0 ≠ 1`. Every PI-pinned column is `0` (matching the all-zero
public inputs); col 5 is the FREE forged column no PI pin catches. -/
def forgeRow : Assignment := fun c => if c = 5 then 1 else 0

/-- **THE HEIGHT-1 FORGE** — a single row (row 0 = first = last), all-zero public inputs. -/
def forgeTrace : VmTrace := { rows := [forgeRow], pub := zeroAsg, tf := forgeTf }

/-- The forge row VIOLATES commitment binding: `COMMITMENT (col 5) = 1 ≠ 0 = COMMITMENT_FULL (col 54)`
— the exact non-satisfying content the last-row `.gate` fails to reject. -/
theorem forge_breaks_commitment_binding : (envAt forgeTrace 0).loc 5 ≠ (envAt forgeTrace 0).loc 54 := by
  decide

/-- The forge's memory / map logs are empty (the note-spend leaf declares no mem/map ops). -/
theorem forge_memLog : Dregg2.Circuit.DescriptorIR2.memLog noteSpendLeafDesc forgeTrace = [] := rfl
theorem forge_mapLog : Dregg2.Circuit.DescriptorIR2.mapLog noteSpendLeafDesc forgeTrace = [] := rfl

/-- **NON-VACUITY POLE — the forge IS accepted under the CURRENT descriptor.** The single-row
`forgeTrace` SATISFIES the whole (buggy) `noteSpendLeafDesc`: the 12 chip lookups land in the table,
every base `.gate` is VACUOUS on the last row (isLast=true), the C7 window is vacuous (on_transition),
and the eight PI pins close on `forgeRow`/`zeroAsg` — even though `col5 ≠ col54`
(`forge_breaks_commitment_binding`). This turns the prose double-spend/commitment-freedom hole into a
PROVEN acceptance: the exact witness the fix must reject. -/
theorem forgeTrace_satisfied2 :
    Satisfied2 (fun _ => 0) noteSpendLeafDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeTrace := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hc2 : c ∈ noteSpendConstraints := hc
    have hi2 : i < 1 := hi
    interval_cases i <;>
      (fin_cases hc2 <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
          Lookup.holdsAt, unlessSite, whenSite] <;>
        first
          | trivial
          | decide
          | (intro _; decide))
  · intro i hi; trivial
  · intro i hi r hr; simp only [noteSpendLeafDesc] at hr; cases hr
  · intro op hop; rw [forge_memLog] at hop; simp at hop
  · rw [forge_memLog]; exact (by decide)
  · rw [forge_memLog]; exact Dregg2.Circuit.DescriptorIR2.memCheck_nil _ _
  · rw [forge_memLog]; rfl
  · rw [forge_mapLog]; rfl

/-- **THE REGRESSION GATE — the forge is REJECTED under the FIXED descriptor.** The appended
`.base (.boundary VmRow.last (invEqGate IS_MERKLE 5 54))` fires on the single (last) row: with
`is_merkle = 0` it forces `col5 - col54 = 0`, i.e. `1 = 0`. So the exact witness
`forgeTrace_satisfied2` accepts is no longer `Satisfied2` — the `.gate`-vacuity forge is closed. -/
theorem forge_rejected_by_fix (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    ¬ Satisfied2 hash noteSpendLeafDescFixed minit mfin maddrs forgeTrace := by
  intro h
  have hmem : VmConstraint2.base (.boundary VmRow.last (invEqGate IS_MERKLE 5 54))
      ∈ noteSpendLeafDescFixed.constraints := by
    show _ ∈ noteSpendConstraints ++ noteSpendLastRowFix
    apply List.mem_append_right
    simp only [noteSpendLastRowFix, List.mem_cons]; tauto
  have hc := h.rowConstraints 0 (by decide) _ hmem
  have hislast : ((0 : Nat) + 1 == forgeTrace.rows.length) = true := by decide
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  have hbody := hc hislast
  revert hbody; decide

/-! ## §12 — THE RUNG-2 NO-FORGERY UPGRADE: the fixed descriptor binds `COMMITMENT` on EVERY row.

The fix's no-forgery tooth, stated over the FIXED descriptor: ANY satisfying trace binds `COMMITMENT
(col 5) = COMMITMENT_FULL (col 54)` on its LAST row too (when that row is a spend row) — the binding
the transition `.gate` alone leaves free. `forge_rejected_by_fix` is its permanent non-vacuity pole
(a concrete last row where the binding FAILS is rejected), and `witnessTrace_satisfied2` witnesses the
positive pole (an honest trace still satisfies the fixed descriptor — proved in `§13`). -/

/-- **`fixed_commitment_binds_last` — THE FIXED DESCRIPTOR'S LAST-ROW COMMITMENT BINDING.** A trace
that satisfies `noteSpendLeafDescFixed` has `COMMITMENT (col 5) = COMMITMENT_FULL (col 54)` on its LAST
row whenever that row is a spend row (`is_merkle = 0`). This is the property `noteSpendLeafDesc` LACKS
(exploited by `forgeTrace`); the appended `VmRow.last` boundary supplies it. Composed with the
existing every-transition-row binding, `COMMITMENT` is now bound on EVERY row of the fixed descriptor
— matching the deployed every-row `assert_zero`. -/
theorem fixed_commitment_binds_last {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendLeafDescFixed minit mfin maddrs t)
    (hlen : 0 < t.rows.length)
    (hspendLast : (envAt t (t.rows.length - 1)).loc IS_MERKLE = 0)
    (hcanon5 : Canon ((envAt t (t.rows.length - 1)).loc 5))
    (hcanon54 : Canon ((envAt t (t.rows.length - 1)).loc 54)) :
    (envAt t (t.rows.length - 1)).loc 5 = (envAt t (t.rows.length - 1)).loc 54 := by
  have hidx : t.rows.length - 1 < t.rows.length := by omega
  have hmem : VmConstraint2.base (.boundary VmRow.last (invEqGate IS_MERKLE 5 54))
      ∈ noteSpendLeafDescFixed.constraints := by
    show _ ∈ noteSpendConstraints ++ noteSpendLastRowFix
    apply List.mem_append_right
    simp only [noteSpendLastRowFix, List.mem_cons]; tauto
  have hc := hsat.rowConstraints (t.rows.length - 1) hidx _ hmem
  have hislast : ((t.rows.length - 1) + 1 == t.rows.length) = true := by
    have he : (t.rows.length - 1) + 1 = t.rows.length := by omega
    rw [he]; exact beq_self_eq_true _
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  exact invEqGate_spend (envAt t (t.rows.length - 1)) hspendLast 5 54 hcanon5 hcanon54 (hc hislast)

/-! ## §13 — the FIXED descriptor still ACCEPTS the honest witness (the fix is not over-tight).

An HONEST trace's LAST row is a PADDING row with `is_merkle = 1` (the deployed generator,
`note_spending.rs:680`), so each appended `InvertedGated` boundary `(1 − is_merkle)·body = 0·body = 0`
is INERT there, and the `binaryGate`/`posGate` boundaries close on the padding row's booleans. So the
fix rejects the height-1 forge WITHOUT rejecting any honest spend. `witnessTrace` (RUNG-1's concrete
2-row witness) demonstrates: its last row carries `witnessAsg` with `is_merkle = 0` — but that is the
`is_merkle = 0` DEGENERATE witness, so we show acceptance for the shape where the last row satisfies
the boundaries directly. -/

/-- The fixed descriptor's last-row boundaries all VANISH on RUNG-1's `witnessAsg` row (every body is
`0` there: `is_merkle = 0` makes each `InvertedGated` body `1·(a−b)` with `a = b = 0`, `binaryGate
0·(0−1) = 0`, `posGate` at `pos = 0` is `0`) — so appending them keeps `witnessTrace` satisfying. -/
theorem witnessAsg_last_boundaries_vanish :
    (binaryGate IS_MERKLE).eval witnessAsg = 0
    ∧ (invEqGate IS_MERKLE 5 54).eval witnessAsg = 0
    ∧ (invEqGate IS_MERKLE 1 28).eval witnessAsg = 0
    ∧ (invEqGate IS_MERKLE 19 29).eval witnessAsg = 0
    ∧ (invEqGate IS_MERKLE 2 30).eval witnessAsg = 0
    ∧ posGate.eval witnessAsg = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The FIXED descriptor still ACCEPTS the honest witness.** RUNG-1's concrete `witnessTrace`
satisfies `noteSpendLeafDescFixed` too: it satisfies every original constraint
(`witnessTrace_satisfied2`) and the six appended `VmRow.last` boundaries vanish on its rows
(`witnessAsg_last_boundaries_vanish`). The positive pole survives the fix. -/
theorem fixed_accepts_honest_witness :
    Satisfied2 (fun _ => 0) noteSpendLeafDescFixed (fun _ => 0) (fun _ => (0, 0)) [] witnessTrace := by
  obtain ⟨hbin, h554, h128, h1929, h230, hpos⟩ := witnessAsg_last_boundaries_vanish
  have hbase := witnessTrace_satisfied2
  have hml : Dregg2.Circuit.DescriptorIR2.memLog noteSpendLeafDescFixed witnessTrace = [] := rfl
  have hmapl : Dregg2.Circuit.DescriptorIR2.mapLog noteSpendLeafDescFixed witnessTrace = [] := rfl
  refine ⟨?_, hbase.rowHashes, hbase.rowRanges, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    -- `c` is either an original constraint or one of the six appended boundaries.
    have hcc : c ∈ noteSpendConstraints ++ noteSpendLastRowFix := hc
    rcases List.mem_append.mp hcc with hc0 | hcfix
    · exact hbase.rowConstraints i hi c hc0
    · -- the appended boundaries: on either row the body vanishes on `witnessAsg`.
      have hrow : (envAt witnessTrace i).loc = witnessAsg := by
        have hi2 : i < 2 := hi
        interval_cases i <;> rfl
      fin_cases hcfix <;>
        (simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]; intro _; rw [hrow]; assumption)
  · intro op hop; rw [hml] at hop; simp at hop
  · rw [hml]; exact (by decide)
  · rw [hml]; exact Dregg2.Circuit.DescriptorIR2.memCheck_nil _ _
  · rw [hml]; rfl
  · rw [hmapl]; rfl

#assert_axioms forgeTrace_satisfied2
#assert_axioms forge_rejected_by_fix
#assert_axioms fixed_commitment_binds_last
#assert_axioms fixed_accepts_honest_witness

/-! ## §14 — shape pins for the forge / fix. -/
#guard decide (forgeTrace.rows.length = 1)
#guard decide (noteSpendLeafDescFixed.constraints.length = 33)

end Dregg2.Circuit.Emit.NoteSpendingLeafRung2
