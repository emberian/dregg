/-
# Dregg2.Circuit.Emit.DyckStackBound — binding the Dyck parse to its `table` / `route` public inputs
(L2).

Lane E, `docs/automata/SUBSTRATE-DECISION.md` §5.2. 2026-11-06.

## The family

`DyckStackEmit.dyckParseDesc` (served as `dregg-dyck-parse-v1`): the leftmost pushdown replay of
`S → [S] | ε`, with four PIs: `initial_symbol`, `input_len`, `table_commitment` (the running-hash
seed) and `route_commitment` (the last row's running hash). Per row an arity-4 chip lookup binds
`ENTRY_HASH = H(RULE_ID, STACK0, INPUT_TOKEN, LANE_ZERO)` and an arity-2 one binds
`RUNNING_HASH = H(ACC, ENTRY_HASH)`, `ACC` copied forward and seeded at `pi[table]`.
`DyckStackReplay.parse_sat_imp_replay_emit_unconditional` concludes that the word READ OFF THE TRACE
(`decodedWord t n`) is accepted by the replay; it goes through the projection `dyckDesc`, which
transcribes the chain out, so the `table`/`route` PIs appear in no theorem.

## What is proved

  * `dyck_route_eq_fold` — `pi[route] = chainFold pi[table] (entry-hash column)`: the two chip
    lookups (sound chip table), the copy-forward window, the seed and route pins.
  * `dyck_route_binds_rows` — two satisfying traces with the same `table` and `route` PIs and the
    same length have the same entry preimage `(RULE_ID, STACK0, INPUT_TOKEN, LANE_ZERO)` on every
    row (CR through the fold, then through each entry).
  * ⚑ `dyck_route_binds_word` — and therefore the same halting row and the same PARSED WORD: on a
    transition row the selectors are a function of `STACK0` (`S` ↔ rule, `op`/`cl` ↔ term,
    `EMPTY` ↔ done), so the decoded word is a function of the bound column.
  * ⚑ `dyck_bound` — the content-bound statement: the parsed word is accepted by the Dyck replay
    AND any other satisfying trace with the same `(table, route, length)` parses the same word.
    For an intended record `E` read by a reference trace with those publics, this trace reads `E`.

## Finding: the route cannot be recomputed from the record [READ]

`RULE_ID` is constrained only on rule rows and `INPUT_TOKEN` only on term rows (every tooth on them
is gated by `IS_RULE` / `IS_TERM`), yet both enter every row's entry hash. So two honest parses of
one word can publish different routes, and a verifier holding the record cannot compute the route
it should expect: there is no function `record ↦ route` for this descriptor, and the bound
statement above is in the two-trace (anchor) form, not the `commit w = c` form. What the AIR would
need for the record form: two gates `(1 − IS_RULE)·RULE_ID` and `(1 − IS_TERM)·INPUT_TOKEN` (the
free cells pinned to zero off their rows), plus a fixed padding rule after `done`; then
`route = chainFold table (canonical entries of w)` is a function of `w`. Not added here.

## Falsifier (§4, kernel-checked)

The projection `dyckDesc` (the record-ignoring acceptance: same parse teeth, no chain) accepts the
shipped `"[]"` parse with `pi[route] = 0` AND with `pi[route] = 1` (`proj_accepts_route0`,
`proj_accepts_route1`), and the unbound replay theorem fires on both. Under the bound descriptor the
route is a function of the rows (`route_function_of_rows`), so at most one of the two claims can be
the route of that parse.

## NOT claimed
  * No satisfying witness of the FULL `dyckParseDesc` (with its chip table) is constructed here; the
    binding theorems' chain hypotheses (`ChipTableSound`, `CollisionFree`, the PI canonicality) are
    the ones `DfaRoutingRung2` inhabits for the routing chain, and the parse teeth are inhabited by
    `DyckStackRefine.witTrace`. A full-descriptor witness is the named follow-up.
  * The grammar is the single-nesting `S → [S] | ε` (one word per even length), so `input_len`
    alone already determines an accepted word [INFERRED from the grammar; not proved here]; the
    route binds the derivation (rules and junk cells), which is what a general grammar needs.

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.DyckStackReplay
import Dregg2.Circuit.Emit.DfaRoutingRung2

namespace Dregg2.Circuit.Emit.DyckStackBound

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Circuit.ChipNarrowLookup (narrowTable chip_lookup_narrow_sound_of_wide_table)
open Dregg2.Circuit.Emit.DyckStackRefine
open Dregg2.Circuit.Emit.DyckStackReplay
open Dregg2.Circuit.Emit.DfaRoutingRung2 (dfaPrims collisionFree_of_injective)
open Dregg2.Crypto.DfaAcceptanceAir (CollisionFree runningFold fold_inj)

set_option autoImplicit false


/-! ## §1 — The chain, extracted from the byte-pinned descriptor. -/

/-- The running fold of the chain: `chainFold s (e :: es) = chainFold (H[s, e]) es`. -/
def chainFold (hash : List ℤ → ℤ) : ℤ → List ℤ → ℤ
  | s, [] => s
  | s, e :: es => chainFold hash (hash [s, e]) es

theorem chainFold_eq_runningFold (hash : List ℤ → ℤ) :
    ∀ (s : ℤ) (es : List ℤ), chainFold hash s es = @runningFold ℤ _ (dfaPrims hash) s es
  | _, [] => rfl
  | s, e :: es => chainFold_eq_runningFold hash (hash [s, e]) es

theorem mem_entry : DyckStackEmit.entryHashLookup ∈ DyckStackEmit.dyckParseDesc.constraints := by emit_mem
theorem mem_running : DyckStackEmit.runningHashLookup ∈ DyckStackEmit.dyckParseDesc.constraints := by emit_mem
theorem mem_copy : DyckStackEmit.copyForwardWindow ∈ DyckStackEmit.dyckParseDesc.constraints := by emit_mem
theorem mem_seed : DyckStackEmit.seedAccPin ∈ DyckStackEmit.dyckParseDesc.constraints := by emit_mem
theorem mem_route :
    VmConstraint2.base (.piBinding VmRow.last DyckStackEmit.RUNNING_HASH DyckStackEmit.PI_ROUTE)
      ∈ DyckStackEmit.dyckParseDesc.constraints := by emit_mem

/-- The entry preimage of a row. -/
def pre (a : Assignment) : List ℤ := [a RULE_ID, a (stk 0), a INPUT_TOKEN, a LANE_ZERO]

theorem getD_eq {t : VmTrace} {i : Nat} (hi : i < t.rows.length) :
    t.rows.getD i zeroAsg = t.rows[i]'hi := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

section Extract
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable (hsat : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t)
variable (hchip : ChipTableSound hash (t.tf .poseidon2))
variable (hwire : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2))

include hsat hchip hwire in
theorem entry_eq {i : Nat} (hi : i < t.rows.length) :
    (t.rows[i]'hi) DyckStackEmit.ENTRY_HASH = hash (pre (t.rows[i]'hi)) := by
  have hrc := hsat.rowConstraints i hi _ mem_entry
  have hl : (envAt t i).loc = t.rows[i]'hi := getD_eq hi
  have h0 : (chipLookupTupleNarrow [.var DyckStackEmit.RULE_ID, .var (DyckStackEmit.stk 0),
      .var DyckStackEmit.INPUT_TOKEN, .var DyckStackEmit.LANE_ZERO] DyckStackEmit.ENTRY_HASH).map
      (·.eval (t.rows[i]'hi)) ∈ t.tf poseidon2narrow := by
    simpa only [VmConstraint2.holdsAt, DyckStackEmit.entryHashLookup, Lookup.holdsAt, hl] using hrc
  rw [hwire] at h0
  have h := chip_lookup_narrow_sound_of_wide_table hash (t.tf .poseidon2) hchip (t.rows[i]'hi)
    _ _ (by decide) h0
  simpa only [List.map_cons, List.map_nil, EmittedExpr.eval, pre] using h

include hsat hchip hwire in
theorem running_eq {i : Nat} (hi : i < t.rows.length) :
    (t.rows[i]'hi) DyckStackEmit.RUNNING_HASH
      = hash [(t.rows[i]'hi) DyckStackEmit.ACC, (t.rows[i]'hi) DyckStackEmit.ENTRY_HASH] := by
  have hrc := hsat.rowConstraints i hi _ mem_running
  have hl : (envAt t i).loc = t.rows[i]'hi := getD_eq hi
  have h0 : (chipLookupTupleNarrow [.var DyckStackEmit.ACC, .var DyckStackEmit.ENTRY_HASH]
      DyckStackEmit.RUNNING_HASH).map (·.eval (t.rows[i]'hi)) ∈ t.tf poseidon2narrow := by
    simpa only [VmConstraint2.holdsAt, DyckStackEmit.runningHashLookup, Lookup.holdsAt, hl] using hrc
  rw [hwire] at h0
  have h := chip_lookup_narrow_sound_of_wide_table hash (t.tf .poseidon2) hchip (t.rows[i]'hi)
    _ _ (by decide) h0
  simpa only [List.map_cons, List.map_nil, EmittedExpr.eval] using h

end Extract

/-- Canonicality of the two chain PIs (the cells are covered by `DyckCanon`). -/
def ChainPiCanon (t : VmTrace) : Prop :=
  Canon (t.pub DyckStackEmit.PI_TABLE) ∧ Canon (t.pub DyckStackEmit.PI_ROUTE)

theorem eq_of_canon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921]) (ha : Canon a) (hb : Canon b) :
    a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

/-- The fold along a list of rows with the chain's recursion. -/
theorem last_running_fold (hash : List ℤ → ℤ) : ∀ (l : List Assignment) (s : ℤ) (hne : l ≠ []),
    (∀ a ∈ l, a DyckStackEmit.RUNNING_HASH = hash [a DyckStackEmit.ACC, a DyckStackEmit.ENTRY_HASH]) →
    (∀ a₀, l.head? = some a₀ → a₀ DyckStackEmit.ACC = s) →
    (∀ i (h : i + 1 < l.length), (l[i + 1]) DyckStackEmit.ACC = (l[i]) DyckStackEmit.RUNNING_HASH) →
    (l.getLast hne) DyckStackEmit.RUNNING_HASH = chainFold hash s (l.map (· DyckStackEmit.ENTRY_HASH))
  | [a], s, _, hr, hs, _ => by
    simp only [List.getLast_singleton, List.map_cons, List.map_nil, chainFold]
    rw [hr a List.mem_cons_self, hs a rfl]
  | a :: b :: rest, s, _, hr, hs, hc => by
    rw [List.getLast_cons (by simp), List.map_cons, chainFold]
    have ha : a DyckStackEmit.RUNNING_HASH = hash [s, a DyckStackEmit.ENTRY_HASH] := by
      rw [hr a List.mem_cons_self, hs a rfl]
    rw [← ha]
    refine last_running_fold hash (b :: rest) _ (by simp)
      (fun x hx => hr x (List.mem_cons_of_mem _ hx)) (fun a₀ h₀ => ?_) (fun i hi => ?_)
    · simp only [List.head?_cons, Option.some.injEq] at h₀
      subst h₀
      exact hc 0 (by simp)
    · exact hc (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)

/-- ⚑ **`dyck_route_eq_fold`** — the route PI is the fold of the entry-hash column, seeded at the
table PI. -/
theorem dyck_route_eq_fold {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2))
    (hcanon : DyckCanon t) (hpi : ChainPiCanon t) (hne : t.rows ≠ []) :
    t.pub DyckStackEmit.PI_ROUTE
      = chainFold hash (t.pub DyckStackEmit.PI_TABLE) (t.rows.map (· DyckStackEmit.ENTRY_HASH)) := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have canonRow : ∀ i (hi : i < t.rows.length) c, Canon ((t.rows[i]'hi) c) := by
    intro i hi c
    have := hcanon.cells i c
    rwa [getD_eq hi] at this
  -- the seed pin, lifted
  have hseed : ∀ a₀, t.rows.head? = some a₀ → a₀ DyckStackEmit.ACC = t.pub DyckStackEmit.PI_TABLE := by
    intro a₀ h₀
    have h0 : t.rows[0]'hpos = a₀ := by
      rw [List.head?_eq_some_head hne] at h₀
      rw [← Option.some.inj h₀, List.head_eq_getElem hne]
    have hrc := hsat.rowConstraints 0 hpos _ mem_seed
    simp only [DyckStackEmit.seedAccPin, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hrc
    have hm := hrc (by decide)
    simp only [envAt] at hm
    rw [getD_eq hpos] at hm
    rw [← h0]
    exact eq_of_canon hm (canonRow 0 hpos _) hpi.1
  -- the copy-forward window, lifted
  have hcopy : ∀ i (h : i + 1 < t.rows.length),
      (t.rows[i + 1]) DyckStackEmit.ACC = (t.rows[i]'(Nat.lt_of_succ_lt h)) DyckStackEmit.RUNNING_HASH := by
    intro i hi
    have hi0 : i < t.rows.length := Nat.lt_of_succ_lt hi
    have hrc := hsat.rowConstraints i hi0 _ mem_copy
    have hlf : (i + 1 == t.rows.length) = false := by simpa using Nat.ne_of_lt hi
    have h2 : WindowConstraint.holdsAt (envAt t i) (i + 1 == t.rows.length)
        ⟨DyckStackEmit.copyForwardBody, true⟩ := hrc
    simp only [WindowConstraint.holdsAt, if_true] at h2
    have hw := h2 hlf
    have hcm : (envAt t i).nxt DyckStackEmit.ACC ≡ (envAt t i).loc DyckStackEmit.RUNNING_HASH [ZMOD 2013265921] :=
      (gate_modEq_iff (by
        simp only [DyckStackEmit.copyForwardBody_eq, WindowExpr.eval]; ring)).mp hw
    simp only [envAt] at hcm
    rw [getD_eq hi, getD_eq hi0] at hcm
    exact eq_of_canon hcm (canonRow _ hi _) (canonRow _ hi0 _)
  have hfold := last_running_fold hash t.rows _ hne
    (fun a ha => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      exact running_eq hsat hchip hwire hi) hseed hcopy
  -- the route pin, lifted
  have hrc := hsat.rowConstraints (t.rows.length - 1) hlt _ mem_route
  have hlast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hpos]; exact beq_self_eq_true _
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hrc
  have hm := hrc hlast
  simp only [envAt] at hm
  rw [getD_eq hlt] at hm
  have hZ := eq_of_canon hm (canonRow _ hlt _) hpi.2
  rw [← hZ, ← List.getLast_eq_getElem hne]
  exact hfold

/-! ## §2 — Binding: the publics determine the entry preimages, hence the parsed word. -/

/-- ⚑ **`dyck_route_binds_rows`** — two satisfying traces with the same `table` / `route` PIs and
the same length have the same entry preimage on every row. -/
theorem dyck_route_binds_rows {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t₁ t₂ : VmTrace}
    (cf : @CollisionFree ℤ _ (dfaPrims hash))
    (h₁ : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t₁) (h₂ : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t₂)
    (hc₁ : ChipTableSound hash (t₁.tf .poseidon2)) (hc₂ : ChipTableSound hash (t₂.tf .poseidon2))
    (hw₁ : t₁.tf poseidon2narrow = narrowTable (t₁.tf .poseidon2))
    (hw₂ : t₂.tf poseidon2narrow = narrowTable (t₂.tf .poseidon2))
    (hk₁ : DyckCanon t₁) (hk₂ : DyckCanon t₂) (hp₁ : ChainPiCanon t₁) (hp₂ : ChainPiCanon t₂)
    (hne : t₁.rows ≠ []) (hlen : t₁.rows.length = t₂.rows.length)
    (htab : t₁.pub DyckStackEmit.PI_TABLE = t₂.pub DyckStackEmit.PI_TABLE)
    (hroute : t₁.pub DyckStackEmit.PI_ROUTE = t₂.pub DyckStackEmit.PI_ROUTE) :
    t₁.rows.map pre = t₂.rows.map pre := by
  have hne₂ : t₂.rows ≠ [] := by
    intro h; rw [h] at hlen; exact hne (List.length_eq_zero_iff.mp hlen)
  have f₁ := dyck_route_eq_fold h₁ hc₁ hw₁ hk₁ hp₁ hne
  have f₂ := dyck_route_eq_fold h₂ hc₂ hw₂ hk₂ hp₂ hne₂
  rw [chainFold_eq_runningFold] at f₁ f₂
  have hE : t₁.rows.map (· DyckStackEmit.ENTRY_HASH) = t₂.rows.map (· DyckStackEmit.ENTRY_HASH) :=
    @fold_inj ℤ _ (dfaPrims hash) cf _ _ (by simp [hlen]) _ (by rw [← f₁, hroute, f₂, htab])
  have hent : ∀ {t : VmTrace}, Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t →
      ChipTableSound hash (t.tf .poseidon2) → t.tf poseidon2narrow = narrowTable (t.tf .poseidon2) →
      t.rows.map (· DyckStackEmit.ENTRY_HASH) = t.rows.map (fun a => hash (pre a)) := by
    intro t hs hc hw
    apply List.map_congr_left
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact entry_eq hs hc hw hi
  rw [hent h₁ hc₁ hw₁, hent h₂ hc₂ hw₂] at hE
  letI := dfaPrims hash
  have hinj : ∀ l₁ l₂ : List ℤ, hash l₁ = hash l₂ → l₁ = l₂ := cf.compressN_inj
  clear f₁ f₂ hent
  generalize t₁.rows = l₁ at hE
  generalize t₂.rows = l₂ at hE
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => rfl
    | cons _ _ => simp at hE
  | cons a as ih => cases l₂ with
    | nil => simp at hE
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hE ⊢
      exact ⟨hinj _ _ hE.1, ih bs hE.2⟩

/-- On a transition row the term selector is a function of the stack top. -/
theorem term_iff_top {env : VmRowEnv} (rv : DyckRowValid env) :
    env.loc IS_TERM = 1 ↔ (env.loc (stk 0) = SYM_OP ∨ env.loc (stk 0) = SYM_CL) := by
  constructor
  · exact rv.termTopTerminal
  · intro h
    obtain ⟨hR, hT, hD⟩ := rv.kindsBoolean
    rcases hT with hT | hT
    · exfalso
      have hp := rv.kindPartition
      rcases hR with hR | hR
      · have hD1 : env.loc IS_DONE = 1 := by omega
        have := (rv.doneEmpty hD1).1
        rcases h with h | h <;> rw [this] at h <;> exact absurd h (by decide)
      · have := rv.ruleTopIsS hR
        rcases h with h | h <;> rw [this] at h <;> exact absurd h (by decide)
    · exact hT

/-- On a transition row the done selector is a function of the stack top. -/
theorem done_iff_top {env : VmRowEnv} (rv : DyckRowValid env) :
    env.loc IS_DONE = 1 ↔ env.loc (stk 0) = SYM_EMPTY := by
  constructor
  · exact fun h => (rv.doneEmpty h).1
  · intro h
    obtain ⟨hR, hT, hD⟩ := rv.kindsBoolean
    have hp := rv.kindPartition
    rcases hD with hD | hD
    · exfalso
      rcases hR with hR | hR
      · have hT1 : env.loc IS_TERM = 1 := by omega
        rcases rv.termTopTerminal hT1 with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
      · have := rv.ruleTopIsS hR
        rw [this] at h; exact absurd h (by decide)
    · exact hD

/-- ⚑ **`dyck_route_binds_word`** — equal entry preimages on the transition rows give the same
halting row and the same parsed word. -/
theorem dyck_route_binds_word {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t₁ t₂ : VmTrace}
    (h₁ : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t₁) (h₂ : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t₂)
    (hk₁ : DyckCanon t₁) (hk₂ : DyckCanon t₂)
    (hpre : t₁.rows.map pre = t₂.rows.map pre)
    (n₁ n₂ : Nat) (hn₁ : n₁ + 1 < t₁.rows.length) (hn₂ : n₂ + 1 < t₂.rows.length)
    (hd₁ : (envAt t₁ n₁).loc IS_DONE = 1) (hl₁ : ∀ i, i < n₁ → (envAt t₁ i).loc IS_DONE = 0)
    (hd₂ : (envAt t₂ n₂).loc IS_DONE = 1) (hl₂ : ∀ i, i < n₂ → (envAt t₂ i).loc IS_DONE = 0) :
    n₁ = n₂ ∧ decodedWord t₁ n₁ = decodedWord t₂ n₂ := by
  have hlen : t₁.rows.length = t₂.rows.length := by
    simpa using congrArg List.length hpre
  have rv₁ := fun i (hi : i + 1 < t₁.rows.length) =>
    dyck_sat_imp_row_valid (sat_emit_imp_sat_dyck h₁) hk₁ i hi
  have rv₂ := fun i (hi : i + 1 < t₂.rows.length) =>
    dyck_sat_imp_row_valid (sat_emit_imp_sat_dyck h₂) hk₂ i hi
  -- the stack tops agree on every row
  have htop : ∀ i, i < t₁.rows.length → (envAt t₁ i).loc (stk 0) = (envAt t₂ i).loc (stk 0) := by
    intro i hi
    have hi₂ : i < t₂.rows.length := hlen ▸ hi
    have := congrArg (fun l => l[i]?) hpre
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi₂,
      Option.map_some, Option.some.injEq, pre, List.cons.injEq] at this
    simp only [envAt, getD_eq hi, getD_eq hi₂]
    exact this.2.1
  have doneEq : ∀ i, i + 1 < t₁.rows.length →
      ((envAt t₁ i).loc IS_DONE = 1 ↔ (envAt t₂ i).loc IS_DONE = 1) := by
    intro i hi
    rw [done_iff_top (rv₁ i hi), done_iff_top (rv₂ i (hlen ▸ hi)), htop i (by omega)]
  have hn : n₁ = n₂ := by
    rcases Nat.lt_trichotomy n₁ n₂ with h | h | h
    · exfalso
      have := (doneEq n₁ hn₁).mp hd₁
      rw [hl₂ n₁ h] at this; exact absurd this (by decide)
    · exact h
    · exfalso
      have := (doneEq n₂ (by omega)).mpr hd₂
      rw [hl₁ n₂ h] at this; exact absurd this (by decide)
  subst hn
  refine ⟨rfl, ?_⟩
  have htok : ∀ i, i < n₁ → rowTok t₁ i = rowTok t₂ i := by
    intro i hi
    have hi1 : i + 1 < t₁.rows.length := by omega
    have e1 := term_iff_top (rv₁ i hi1)
    have e2 := term_iff_top (rv₂ i (hlen ▸ hi1))
    rw [htop i (by omega)] at e1
    simp only [rowTok, tokenBrk]
    by_cases ht : (envAt t₂ i).loc IS_TERM = 1
    · rw [if_pos (e1.mpr (e2.mp ht)), if_pos ht, htop i (by omega)]
    · have : ¬ (envAt t₁ i).loc IS_TERM = 1 := fun h => ht (e2.mpr (e1.mp h))
      rw [if_neg this, if_neg ht]
  simp only [decodedWord, decodeWordSeg]
  apply List.filterMap_congr
  intro i hi
  simp only [List.mem_range'] at hi
  exact htok i (by omega)

/-- ⚑ **`dyck_bound` — THE CONTENT-BOUND STATEMENT for the Dyck parse.** A satisfying trace's
parsed word is accepted by the Dyck replay, and it is the word of every other satisfying trace with
the same `(table, route, length)` — in particular of a reference trace reading an intended record. -/
theorem dyck_bound {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t g : VmTrace}
    (cf : @CollisionFree ℤ _ (dfaPrims hash))
    (ht : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t) (hg : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs g)
    (hct : ChipTableSound hash (t.tf .poseidon2)) (hcg : ChipTableSound hash (g.tf .poseidon2))
    (hwt : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2))
    (hwg : g.tf poseidon2narrow = narrowTable (g.tf .poseidon2))
    (hkt : DyckCanon t) (hkg : DyckCanon g) (hpt : ChainPiCanon t) (hpg : ChainPiCanon g)
    (hlen : t.rows.length = g.rows.length)
    (htab : t.pub DyckStackEmit.PI_TABLE = g.pub DyckStackEmit.PI_TABLE)
    (hroute : t.pub DyckStackEmit.PI_ROUTE = g.pub DyckStackEmit.PI_ROUTE)
    (hpi : t.pub PI_INITIAL = SYM_S)
    (n m : Nat) (hn : n + 1 < t.rows.length) (hm : m + 1 < g.rows.length) (hnp : n < 2013265921)
    (hdn : (envAt t n).loc IS_DONE = 1) (hln : ∀ i, i < n → (envAt t i).loc IS_DONE = 0)
    (hdm : (envAt g m).loc IS_DONE = 1) (hlm : ∀ i, i < m → (envAt g i).loc IS_DONE = 0) :
    Dregg2.Crypto.CfgCompact.ReplayAccepts Dregg2.Crypto.Cfg.Reference.dyck
        (rulesOf (decodeRun (decodedWord t n) t (n + 1))) (decodedWord t n) ∧
      decodedWord t n = decodedWord g m := by
  refine ⟨parse_sat_imp_replay_emit_unconditional ht hkt n hn hnp hpi hdn hln, ?_⟩
  have hne : t.rows ≠ [] := by intro h; rw [h] at hn; simp at hn
  have hpre := dyck_route_binds_rows cf ht hg hct hcg hwt hwg hkt hkg hpt hpg hne hlen htab hroute
  exact (dyck_route_binds_word ht hg hkt hkg hpre n m hn hm hdn hln hdm hlm).2

/-- Under the bound descriptor the route is a function of the rows and the table PI. -/
theorem route_function_of_rows {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t₁ t₂ : VmTrace}
    (h₁ : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t₁) (h₂ : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t₂)
    (hc₁ : ChipTableSound hash (t₁.tf .poseidon2)) (hc₂ : ChipTableSound hash (t₂.tf .poseidon2))
    (hw₁ : t₁.tf poseidon2narrow = narrowTable (t₁.tf .poseidon2))
    (hw₂ : t₂.tf poseidon2narrow = narrowTable (t₂.tf .poseidon2))
    (hk₁ : DyckCanon t₁) (hk₂ : DyckCanon t₂) (hp₁ : ChainPiCanon t₁) (hp₂ : ChainPiCanon t₂)
    (hne : t₁.rows ≠ []) (hrows : t₁.rows = t₂.rows)
    (htab : t₁.pub DyckStackEmit.PI_TABLE = t₂.pub DyckStackEmit.PI_TABLE) :
    t₁.pub DyckStackEmit.PI_ROUTE = t₂.pub DyckStackEmit.PI_ROUTE := by
  rw [dyck_route_eq_fold h₁ hc₁ hw₁ hk₁ hp₁ hne,
    dyck_route_eq_fold h₂ hc₂ hw₂ hk₂ hp₂ (hrows ▸ hne), hrows, htab]

/-! ## §4 — The falsifier: the chain-free projection accepts any route claim. -/

/-- The shipped `"[]"` parse with its route PI set to `c`. -/
def witRoute (c : ℤ) : VmTrace :=
  { witTrace with pub := fun i => if i = DyckStackEmit.PI_ROUTE then c else witTrace.pub i }

theorem witRoute_mem (c : ℤ) : memLog dyckDesc (witRoute c) = [] := by rfl
theorem witRoute_map (c : ℤ) : mapLog dyckDesc (witRoute c) = [] := by rfl

theorem proj_accepts (c : ℤ)
    (hd : Dregg2.Circuit.DecideSatisfied2.decideRowConstraints2 (fun _ _ => false)
      (fun _ => (0 : ℤ)) dyckDesc (witRoute c) = true) :
    Satisfied2 (fun _ => (0 : ℤ)) dyckDesc (fun _ => 0) (fun _ => (0, 0)) [] (witRoute c) := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_,
      memClosed := ?_, memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_,
      mapTableFaithful := ?_ }
  · exact witRowConstraints hd
  · intro i _; exact True.intro
  · intro i _ r hr; exact absurd hr List.not_mem_nil
  · exact List.nodup_nil
  · intro op hop; rw [witRoute_mem] at hop; exact absurd hop List.not_mem_nil
  · rw [witRoute_mem]; decide
  · rw [witRoute_mem]; decide
  · rw [witRoute_mem]; rfl
  · rw [witRoute_map]; rfl

/-- The projection ACCEPTS the parse claiming route `0` … -/
theorem proj_accepts_route0 :
    Satisfied2 (fun _ => (0 : ℤ)) dyckDesc (fun _ => 0) (fun _ => (0, 0)) [] (witRoute 0) :=
  proj_accepts 0 (by decide)

/-- … and claiming route `1`: the route PI is unread by the record-ignoring acceptance. -/
theorem proj_accepts_route1 :
    Satisfied2 (fun _ => (0 : ℤ)) dyckDesc (fun _ => 0) (fun _ => (0, 0)) [] (witRoute 1) :=
  proj_accepts 1 (by decide)

/-- The two claims are distinct routes for the same rows and table; under the bound descriptor at
most one of them is the parse's route (`route_function_of_rows`). -/
theorem witRoute_same_rows : (witRoute 0).rows = (witRoute 1).rows ∧
    (witRoute 0).pub DyckStackEmit.PI_TABLE = (witRoute 1).pub DyckStackEmit.PI_TABLE ∧
    (witRoute 0).pub DyckStackEmit.PI_ROUTE ≠ (witRoute 1).pub DyckStackEmit.PI_ROUTE := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-! ## §5 — axiom tripwires. -/

#assert_all_clean [chainFold_eq_runningFold, mem_entry, mem_running, mem_copy, mem_seed, mem_route,
  getD_eq, entry_eq, running_eq, eq_of_canon, last_running_fold, dyck_route_eq_fold,
  dyck_route_binds_rows, term_iff_top, done_iff_top, dyck_route_binds_word, dyck_bound,
  route_function_of_rows, witRoute_mem, witRoute_map, proj_accepts, proj_accepts_route0,
  proj_accepts_route1, witRoute_same_rows]

end Dregg2.Circuit.Emit.DyckStackBound
