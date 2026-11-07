/-
# Dyck record binding, initiative 1 (2026-11-06)

The served `DyckStackEmit.dyckParseDesc` hashes each row's
`[RULE_ID, STACK0, INPUT_TOKEN, LANE_ZERO]`, then folds those hashes from the table
seed to the route public input. The descriptor now zeros unused rule/token fields
and all four final-row preimage fields (ordinary gates skip the final row).

`recordCore` encodes a record as leading bracket-rule/terminal pairs, an empty
rule, then terminal rows. `recordPre` adds a deterministic power-of-two padding
with at least two done rows. `BoundAccepts` checks the computed route AND row
count. `boundAccepts_sound` concludes that this one trace reads the supplied
record and its reconstructed certificate replays it, OR `recordFind` names an
actual hash collision on the trace/record chains. First-done and live-prefix
facts are DERIVED from the committed encoding, not supplied by a reference trace.

The record-facing Rust consumer is `dyck_stack::verify_record`: it computes the
same public inputs and checks the main proof degree before calling the served
verifier. The native codec correspondence is differential-tested on honest
words; a verified Lean-to-Rust extraction theorem is not asserted here.

Residuals: full descriptor satisfaction, chip-table soundness and narrow/wide
wiring, canonical field cells and table/route PIs, initial symbol S, and
`recordCore.length < p`. The record must have the deterministic row count;
the verifier enforces it. This is soundness of the stronger record-facing
relation, not a completeness/unique-parse theorem for every raw descriptor
trace. `dyck_bound_or_collides` retains the two-trace form, explicitly requiring
first-done rows with successors, equal row counts, and n < p. The old
`dyck_bound` and `dyck_route_binds_rows` are ideal injective-hash compatibility
lemmas, NOT finite-digest collision reductions.

Joint inhabitation: `fullWit_satisfies` supplies the full eight-row bracket
trace and a sound chip table for zeroHash; `fullWit_record_fires` instantiates
all one-trace theorem premises and excludes its exact collision branch.
`fullForged_weak_accepts` / `fullForged_strong_refuses` change only the route PI
of that same populated trace. Its chip/canonicality envelopes still hold.
-/
import Dregg2.Circuit.Emit.DyckStackReplay
import Dregg2.Circuit.Emit.DfaRoutingChainBound

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
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval, pre] at h
  exact h

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

/-- Ideal injective-hash compatibility lemma: two satisfying traces with the same `table` / `route` PIs and
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

/-- The collision extractor names the two actual route chains, including their seed. -/
def routeFind (hash : List ℤ → ℤ) (t₁ t₂ : VmTrace) : List ℤ × List ℤ :=
  DfaRoutingChainBound.chainFind hash (t₁.pub DyckStackEmit.PI_TABLE)
    (t₁.rows.map pre) (t₂.rows.map pre)

/-- Route binding with a local, named collision residual; no globally injective finite hash. -/
theorem dyck_route_binds_rows_or_collides {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t₁ t₂ : VmTrace}
    (h₁ : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t₁)
    (h₂ : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t₂)
    (hc₁ : ChipTableSound hash (t₁.tf .poseidon2)) (hc₂ : ChipTableSound hash (t₂.tf .poseidon2))
    (hw₁ : t₁.tf poseidon2narrow = narrowTable (t₁.tf .poseidon2))
    (hw₂ : t₂.tf poseidon2narrow = narrowTable (t₂.tf .poseidon2))
    (hk₁ : DyckCanon t₁) (hk₂ : DyckCanon t₂) (hp₁ : ChainPiCanon t₁) (hp₂ : ChainPiCanon t₂)
    (hne : t₁.rows ≠ []) (hlen : t₁.rows.length = t₂.rows.length)
    (htab : t₁.pub DyckStackEmit.PI_TABLE = t₂.pub DyckStackEmit.PI_TABLE)
    (hroute : t₁.pub DyckStackEmit.PI_ROUTE = t₂.pub DyckStackEmit.PI_ROUTE) :
    t₁.rows.map pre = t₂.rows.map pre ∨
      Dregg2.Circuit.Poseidon2Binding.SpongeColl hash (routeFind hash t₁ t₂) := by
  have hne₂ : t₂.rows ≠ [] := by
    intro h; rw [h] at hlen; exact hne (List.length_eq_zero_iff.mp hlen)
  have f₁ := dyck_route_eq_fold h₁ hc₁ hw₁ hk₁ hp₁ hne
  have f₂ := dyck_route_eq_fold h₂ hc₂ hw₂ hk₂ hp₂ hne₂
  have entries : ∀ {t : VmTrace}, Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t →
      ChipTableSound hash (t.tf .poseidon2) → t.tf poseidon2narrow = narrowTable (t.tf .poseidon2) →
      t.rows.map (· DyckStackEmit.ENTRY_HASH) = (t.rows.map pre).map hash := by
    intro t hs hc hw
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact entry_eq hs hc hw hi
  rw [entries h₁ hc₁ hw₁, chainFold_eq_runningFold] at f₁
  rw [entries h₂ hc₂ hw₂, chainFold_eq_runningFold] at f₂
  exact DfaRoutingChainBound.chain_binds_or_collides hash _ _ _ (by simpa using hlen)
    (by rw [← f₁, hroute, f₂, htab])

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

/-- Ideal injective-hash compatibility lemma. A satisfying trace's
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

/-- The two-trace content statement with an actual chain collision residual. -/
theorem dyck_bound_or_collides {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t g : VmTrace}
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
      (decodedWord t n = decodedWord g m ∨
        Dregg2.Circuit.Poseidon2Binding.SpongeColl hash (routeFind hash t g)) := by
  refine ⟨parse_sat_imp_replay_emit_unconditional ht hkt n hn hnp hpi hdn hln, ?_⟩
  have hne : t.rows ≠ [] := by intro h; rw [h] at hn; simp at hn
  rcases dyck_route_binds_rows_or_collides ht hg hct hcg hwt hwg hkt hkg hpt hpg hne hlen htab hroute
      with hpre | hc
  · exact Or.inl (dyck_route_binds_word ht hg hkt hkg hpre n m hn hm hdn hln hdm hlm).2
  · exact Or.inr hc

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

/-! ## Record encoding: a fixed parse recipe and a fixed padding policy.

The acceptance wrapper pins both the route and the padded row count computed from
this record. It does not accept an existential reference trace. Malformed words
still have an encoding; satisfaction then proves that the word is in the grammar.
-/

open Dregg2.Crypto.Cfg.Reference (Brk)
open Dregg2.Crypto.Cfg.Reference.Brk (op cl)

def termPre (x : Brk) : List ℤ := [0, symId x, symId x, 0]

def recordCore : List Brk → List (List ℤ)
  | [] => [[2,1,0,0]]
  | op :: w => [1,1,0,0] :: termPre op :: recordCore w
  | cl :: w => [2,1,0,0] :: (cl :: w).map termPre

/-- At least two done rows: the accepting row has a successor, including when
its unpadded action count is already a power of two. -/
def recordRows (w : List Brk) : Nat :=
  max ((recordCore w).length + 2) (2 ^ (Nat.log2 ((recordCore w).length + 1) + 1))

def recordPre (w : List Brk) : List (List ℤ) :=
  recordCore w ++ List.replicate (recordRows w - (recordCore w).length) [0,0,0,0]

def routeOf (hash : List ℤ → ℤ) (seed : ℤ) (w : List Brk) : ℤ :=
  chainFold hash seed ((recordPre w).map hash)

def recordFind (hash : List ℤ → ℤ) (t : VmTrace) (w : List Brk) : List ℤ × List ℤ :=
  DfaRoutingChainBound.chainFind hash (t.pub DyckStackEmit.PI_TABLE) (t.rows.map pre) (recordPre w)

def preTok (p : List ℤ) : Option Brk :=
  if p[1]? = some SYM_OP then some op else if p[1]? = some SYM_CL then some cl else none

theorem preTok_termPre (x : Brk) : preTok (termPre x) = some x := by
  cases x <;> decide

theorem recordCore_decodes (w : List Brk) : (recordCore w).filterMap preTok = w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    cases x with
    | op => simpa [recordCore, List.filterMap_cons, preTok, termPre, symId,
        SYM_OP, SYM_CL] using congrArg (List.cons op) ih
    | cl =>
      simp only [recordCore, List.filterMap_cons, List.filterMap_map]
      have hz : preTok [2,1,0,0] = none := by decide
      rw [hz]
      simp [preTok_termPre]

theorem recordRows_room (w : List Brk) : (recordCore w).length + 2 ≤ recordRows w :=
  Nat.le_max_left _ _

theorem recordPre_length (w : List Brk) : (recordPre w).length = recordRows w := by
  simp only [recordPre, List.length_append, List.length_replicate]
  have := recordRows_room w
  omega

theorem recordPre_prefix (w : List Brk) : (recordPre w).take (recordCore w).length = recordCore w :=
  List.take_left

theorem rowTok_pre {t : VmTrace} {i : Nat} (rv : DyckRowValid (envAt t i)) :
    rowTok t i = preTok (pre (envAt t i).loc) := by
  by_cases ht : (envAt t i).loc IS_TERM = 1
  · rcases rv.termTopTerminal ht with h | h
    · simp [rowTok, ht, tokenBrk, preTok, pre, h, SYM_OP]
    · simp [rowTok, ht, tokenBrk, preTok, pre, h, SYM_OP, SYM_CL]
  · have hop : (envAt t i).loc (stk 0) ≠ SYM_OP := fun h => ht ((term_iff_top rv).mpr (.inl h))
    have hcl : (envAt t i).loc (stk 0) ≠ SYM_CL := fun h => ht ((term_iff_top rv).mpr (.inr h))
    simp [rowTok, ht, preTok, pre, hop, hcl]

theorem rows_prefix {t : VmTrace} {n : Nat} (hn : n ≤ t.rows.length) :
    (List.range' 0 n).map (fun i => (envAt t i).loc) = t.rows.take n := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    have hin : i < n := by simpa using hi
    have hit : i < t.rows.length := by omega
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul, Nat.zero_add,
      List.getElem_take, envAt, getD_eq hit]

theorem decodedWord_pre {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hs : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t)
    (hk : DyckCanon t) (n : Nat) (hn : n < t.rows.length) :
    decodedWord t n = ((t.rows.map pre).take n).filterMap preTok := by
  rw [← List.map_take, List.filterMap_map, ← rows_prefix (Nat.le_of_lt hn), List.filterMap_map]
  unfold decodedWord decodeWordSeg
  apply List.filterMap_congr
  intro i hi
  have hin : i < n := by simpa using hi
  exact rowTok_pre (parse_dyck_sat_imp_row_valid hs hk i (by omega))

/-- One trace opens the canonical record, or the extractor returns a collision
on its actual chain and the record's chain. -/
theorem record_pre_or_collides {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hs : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t)
    (hc : ChipTableSound hash (t.tf .poseidon2))
    (hw : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2))
    (hk : DyckCanon t) (hp : ChainPiCanon t) (w : List Brk)
    (hlen : t.rows.length = recordRows w)
    (hr : t.pub DyckStackEmit.PI_ROUTE = routeOf hash (t.pub DyckStackEmit.PI_TABLE) w) :
    t.rows.map pre = recordPre w ∨
      Dregg2.Circuit.Poseidon2Binding.SpongeColl hash (recordFind hash t w) := by
  have hne : t.rows ≠ [] := by
    intro h; have := recordRows_room w; rw [h] at hlen; simp at hlen; omega
  have hf := dyck_route_eq_fold hs hc hw hk hp hne
  have he : t.rows.map (· DyckStackEmit.ENTRY_HASH) = (t.rows.map pre).map hash := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact entry_eq hs hc hw hi
  rw [he, chainFold_eq_runningFold] at hf
  apply DfaRoutingChainBound.chain_binds_or_collides
  · simpa [recordPre_length] using hlen
  · rw [← hf, hr, routeOf, chainFold_eq_runningFold]

/-- The record-facing acceptance relation: fixed word-to-route and fixed row
count. The first-done and length envelopes are explicit until derived below. -/
def BoundAccepts (hash : List ℤ → ℤ) (t : VmTrace) (w : List Brk) : Prop :=
  Satisfied2 hash DyckStackEmit.dyckParseDesc (fun _ => 0) (fun _ => (0,0)) [] t ∧
  t.rows.length = recordRows w ∧
  t.pub DyckStackEmit.PI_ROUTE = routeOf hash (t.pub DyckStackEmit.PI_TABLE) w

/-- The stronger record relation makes the route a function of the word and
public table seed, including padding; no injectivity assumption is involved. -/
theorem one_word_one_route {hash : List ℤ → ℤ} {t₁ t₂ : VmTrace} {w : List Brk}
    (h₁ : BoundAccepts hash t₁ w) (h₂ : BoundAccepts hash t₂ w)
    (hseed : t₁.pub DyckStackEmit.PI_TABLE = t₂.pub DyckStackEmit.PI_TABLE) :
    t₁.pub DyckStackEmit.PI_ROUTE = t₂.pub DyckStackEmit.PI_ROUTE := by
  rw [h₁.2.2, h₂.2.2, hseed]


theorem recordCore_nonzero (w : List Brk) :
    ∀ p ∈ recordCore w, p[1]? ≠ some (0 : ℤ) := by
  induction w with
  | nil => simp [recordCore]
  | cons x w ih =>
    cases x with
    | op =>
      intro p hp
      simp only [recordCore, List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · decide
      · decide
      · exact ih p hp
    | cl =>
      intro p hp
      simp only [recordCore, List.mem_cons] at hp
      rcases hp with rfl | hp
      · decide
      · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
        cases x <;> decide

theorem recordPre_done (w : List Brk) :
    (recordPre w)[(recordCore w).length]? = some [0,0,0,0] := by
  have hroom := recordRows_room w
  simp [recordPre, show
    0 < recordRows w - (recordCore w).length by omega]

/-- One-trace record soundness. All premises refer to the actual proof trace;
there is no supplied honest trace and no global collision-free hash assumption. -/
theorem boundAccepts_sound {hash : List ℤ → ℤ} {t : VmTrace} {w : List Brk}
    (h : BoundAccepts hash t w) (hc : ChipTableSound hash (t.tf .poseidon2))
    (hw : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2))
    (hk : DyckCanon t) (hp : ChainPiCanon t)
    (hpi : t.pub PI_INITIAL = SYM_S) (hnp : (recordCore w).length < 2013265921) :
    (decodedWord t (recordCore w).length = w ∧
      Dregg2.Crypto.CfgCompact.ReplayAccepts Dregg2.Crypto.Cfg.Reference.dyck
        (rulesOf (decodeRun w t ((recordCore w).length + 1))) w) ∨
      Dregg2.Circuit.Poseidon2Binding.SpongeColl hash (recordFind hash t w) := by
  rcases record_pre_or_collides h.1 hc hw hk hp w h.2.1 h.2.2 with he | hcoll
  · left
    have hroom : (recordCore w).length + 1 < t.rows.length := by
      have := recordRows_room w
      have hlen := h.2.1
      omega
    have hread := decodedWord_pre h.1 hk (recordCore w).length (by omega)
    rw [he, recordPre_prefix, recordCore_decodes] at hread
    have rowPreAt : ∀ i, i < t.rows.length →
        some (pre (envAt t i).loc) = (recordPre w)[i]? := by
      intro i hi
      have hq := congrArg (fun l : List (List ℤ) => l[i]?) he
      simpa only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
        envAt, getD_eq hi] using hq
    have hd : (envAt t (recordCore w).length).loc IS_DONE = 1 := by
      apply (done_iff_top (parse_dyck_sat_imp_row_valid h.1 hk _ hroom)).mpr
      have hx := rowPreAt (recordCore w).length (by omega)
      rw [recordPre_done] at hx
      have heq := Option.some.inj hx
      have := congrArg (fun p : List ℤ => p[1]?) heq
      simpa [pre, SYM_EMPTY] using this
    have hl : ∀ i, i < (recordCore w).length → (envAt t i).loc IS_DONE = 0 := by
      intro i hi
      have hit : i < t.rows.length := by omega
      have rv := parse_dyck_sat_imp_row_valid h.1 hk i (by omega)
      rcases rv.kindsBoolean.2.2 with hz | ho
      · exact hz
      · exfalso
        have hx := rowPreAt i hit
        have hcget : (recordPre w)[i]? = some ((recordCore w)[i]'hi) := by
          simp [recordPre, List.getElem?_append, hi]
        rw [hcget] at hx
        have hpeq := Option.some.inj hx
        have hnz := recordCore_nonzero w _ (List.getElem_mem hi)
        rw [← hpeq] at hnz
        exact hnz (by simp [pre, (rv.doneEmpty ho).1, SYM_EMPTY])
    refine ⟨hread, ?_⟩
    have hr := parse_sat_imp_replay_emit_unconditional h.1 hk (recordCore w).length hroom hnp hpi hd hl
    rwa [hread] at hr
  · exact Or.inr hcoll

/-! ## Joint witness of the full served descriptor and its chain envelopes. -/

/-- A deliberately collision-prone hash suffices for joint inhabitation: no global
injectivity assumption is smuggled into the witness. -/
def zeroHash (_ : List ℤ) : ℤ := 0

def fullInputs : List (List ℤ) :=
  [[1,1,0,0], [0,2,2,0], [2,1,0,0], [0,3,3,0], [0,0,0,0], [0,0]]

def fullChip : Table := fullInputs.map (fun ins => chipRow zeroHash ins (List.replicate 7 0))

def fullTf : TraceFamily := fun id => match id with
  | .poseidon2 => fullChip
  | .custom 3 => narrowTable fullChip
  | _ => []

def fullWit : VmTrace := { witTrace with tf := fullTf }

theorem fullWit_chipSound : ChipTableSound zeroHash (fullWit.tf .poseidon2) := by
  intro r hr
  obtain ⟨ins, hi, rfl⟩ := List.mem_map.mp hr
  refine ⟨ins, List.replicate 7 0, ?_, by decide, rfl⟩
  simp only [fullInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem fullWit_wire : fullWit.tf poseidon2narrow = narrowTable (fullWit.tf .poseidon2) := rfl

theorem fullWit_canon : DyckCanon fullWit := ⟨witTrace_canon.cells⟩

theorem fullWit_piCanon : ChainPiCanon fullWit := by
  constructor <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem fullWit_satisfies :
    Satisfied2 zeroHash DyckStackEmit.dyckParseDesc (fun _ => 0) (fun _ => (0,0)) [] fullWit := by
  have hm := memLog_nil_of dyckParseDesc_memOps fullWit
  have hp := mapLog_nil_of dyckParseDesc_mapOps fullWit
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := List.nodup_nil,
      memClosed := ?_, memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_,
      mapTableFaithful := ?_ }
  · have hd : Dregg2.Circuit.DecideSatisfied2.decideRowConstraints2
        (fun _ _ => false) zeroHash DyckStackEmit.dyckParseDesc fullWit = true := by decide
    rw [Dregg2.Circuit.DecideSatisfied2.decideRowConstraints2, List.all_eq_true] at hd
    intro i hi c hc
    have h2 := hd i (List.mem_range.mpr hi)
    rw [List.all_eq_true] at h2
    exact holdsAt_of_dc2 (h2 c hc)
  · intro i _; trivial
  · intro i _ r hr; exact absurd hr List.not_mem_nil
  · intro op hop; rw [hm] at hop; exact absurd hop List.not_mem_nil
  · rw [hm]; decide
  · rw [hm]; decide
  · rw [hm]; rfl
  · rw [hp]; rfl

/-- The exact extractor, on the exact satisfying trace, has no collision branch. -/
theorem fullWit_no_collision :
    ¬ Dregg2.Circuit.Poseidon2Binding.SpongeColl zeroHash (routeFind zeroHash fullWit fullWit) := by
  intro h
  exact h.1 (DfaRoutingChainBound.chainFind_self _ _ _)

/-- The full descriptor's bound theorem fires on the nonempty bracket word,
with its collision branch disproved for this exact pair of chains. -/
theorem fullWit_binding_fires :
    Dregg2.Crypto.CfgCompact.ReplayAccepts Dregg2.Crypto.Cfg.Reference.dyck
      (rulesOf (decodeRun [Dregg2.Crypto.Cfg.Reference.Brk.op, Dregg2.Crypto.Cfg.Reference.Brk.cl]
        fullWit 5)) [Dregg2.Crypto.Cfg.Reference.Brk.op, Dregg2.Crypto.Cfg.Reference.Brk.cl] := by
  have h := dyck_bound_or_collides fullWit_satisfies fullWit_satisfies
    fullWit_chipSound fullWit_chipSound fullWit_wire fullWit_wire fullWit_canon fullWit_canon
    fullWit_piCanon fullWit_piCanon rfl rfl rfl rfl 4 4 (by decide) (by decide) (by decide)
    (by decide) (by intro i hi; interval_cases i <;> decide)
    (by decide) (by intro i hi; interval_cases i <;> decide)
  exact h.1

theorem fullWit_record : BoundAccepts zeroHash fullWit [op, cl] :=
  ⟨fullWit_satisfies, by decide, by decide⟩

theorem fullWit_record_no_collision :
    ¬ Dregg2.Circuit.Poseidon2Binding.SpongeColl zeroHash (recordFind zeroHash fullWit [op,cl]) := by
  have he : fullWit.rows.map pre = recordPre [op,cl] := by decide
  intro hc
  apply hc.1
  simp only [recordFind, ← he]
  exact DfaRoutingChainBound.chainFind_self _ _ _

/-- The one-trace record theorem fires with every premise jointly instantiated. -/
theorem fullWit_record_fires : decodedWord fullWit 4 = [op,cl] ∧
    Dregg2.Crypto.CfgCompact.ReplayAccepts Dregg2.Crypto.Cfg.Reference.dyck
      (rulesOf (decodeRun [op,cl] fullWit 5)) [op,cl] :=
  (boundAccepts_sound fullWit_record fullWit_chipSound fullWit_wire fullWit_canon
    fullWit_piCanon rfl (by decide)).resolve_right fullWit_record_no_collision

/-- Alter only the route PI of the fully populated witness. -/
def fullForged : VmTrace := { fullWit with pub := (witRoute 1).pub }

/-- The hash-erasing projection really accepts the forged claim. -/
theorem fullForged_weak_accepts :
    Satisfied2 zeroHash dyckDesc (fun _ => 0) (fun _ => (0,0)) [] fullForged := by
  have hm := memLog_nil_of dyckDesc_memOps fullForged
  have hp := mapLog_nil_of dyckDesc_mapOps fullForged
  refine
    { rowConstraints := witRowConstraints (by decide), rowHashes := ?_, rowRanges := ?_,
      memAddrsNodup := List.nodup_nil, memClosed := ?_, memDisciplined := ?_, memBalanced := ?_,
      memTableFaithful := ?_, mapTableFaithful := ?_ }
  · intro i _; trivial
  · intro i _ r hr; exact absurd hr List.not_mem_nil
  · intro op hop; rw [hm] at hop; exact absurd hop List.not_mem_nil
  · rw [hm]; decide
  · rw [hm]; decide
  · rw [hm]; rfl
  · rw [hp]; rfl

/-- The same claim is refused by the full served descriptor's route boundary. -/
theorem fullForged_strong_refuses :
    ¬ Satisfied2 zeroHash DyckStackEmit.dyckParseDesc (fun _ => 0) (fun _ => (0,0)) [] fullForged := by
  intro hs
  have h := hs.rowConstraints 7 (by decide) _ mem_route
  have hf : (7 + 1 == fullForged.rows.length) = true := by decide
  have bad : (0 : ℤ) ≡ 1 [ZMOD 2013265921] := h hf
  exact absurd bad (by decide)

/-- The refusal does not escape through an unsatisfied chip/canonicality envelope. -/
theorem fullForged_envelopes : ChipTableSound zeroHash (fullForged.tf .poseidon2) ∧
    fullForged.tf poseidon2narrow = narrowTable (fullForged.tf .poseidon2) ∧
    DyckCanon fullForged ∧ ChainPiCanon fullForged :=
  ⟨fullWit_chipSound, fullWit_wire, ⟨fullWit_canon.cells⟩, by constructor <;> decide⟩

/-! ## §5 — axiom tripwires. -/

/-- info: 'Dregg2.Circuit.Emit.DyckStackBound.dyck_route_binds_rows_or_collides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dyck_route_binds_rows_or_collides
/-- info: 'Dregg2.Circuit.Emit.DyckStackBound.dyck_bound_or_collides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dyck_bound_or_collides
/-- info: 'Dregg2.Circuit.Emit.DyckStackBound.boundAccepts_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boundAccepts_sound
/-- info: 'Dregg2.Circuit.Emit.DyckStackBound.one_word_one_route' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms one_word_one_route
/-- info: 'Dregg2.Circuit.Emit.DyckStackBound.fullWit_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fullWit_satisfies
/-- info: 'Dregg2.Circuit.Emit.DyckStackBound.fullWit_record_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fullWit_record_fires
/-- info: 'Dregg2.Circuit.Emit.DyckStackBound.fullWit_record_no_collision' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fullWit_record_no_collision
/-- info: 'Dregg2.Circuit.Emit.DyckStackBound.fullForged_weak_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fullForged_weak_accepts
/-- info: 'Dregg2.Circuit.Emit.DyckStackBound.fullForged_strong_refuses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullForged_strong_refuses
/-- info: 'Dregg2.Circuit.Emit.DyckStackBound.fullForged_envelopes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fullForged_envelopes


#assert_all_clean [chainFold_eq_runningFold, mem_entry, mem_running, mem_copy, mem_seed, mem_route,
  getD_eq, entry_eq, running_eq, eq_of_canon, last_running_fold, dyck_route_eq_fold,
  dyck_route_binds_rows, term_iff_top, done_iff_top, dyck_route_binds_word, dyck_bound,
  route_function_of_rows, witRoute_mem, witRoute_map, proj_accepts, proj_accepts_route0,
  proj_accepts_route1, witRoute_same_rows,
  dyck_route_binds_rows_or_collides,
  dyck_bound_or_collides,
  recordCore_decodes,
  recordRows_room,
  recordPre_length,
  recordPre_prefix,
  rowTok_pre,
  rows_prefix,
  decodedWord_pre,
  record_pre_or_collides,
  one_word_one_route,
  recordCore_nonzero,
  recordPre_done,
  boundAccepts_sound,
  fullWit_chipSound,
  fullWit_wire,
  fullWit_canon,
  fullWit_piCanon,
  fullWit_satisfies,
  fullWit_no_collision,
  fullWit_binding_fires,
  fullWit_record,
  fullWit_record_no_collision,
  fullWit_record_fires,
  fullForged_weak_accepts,
  fullForged_strong_refuses,
  fullForged_envelopes]

end Dregg2.Circuit.Emit.DyckStackBound
