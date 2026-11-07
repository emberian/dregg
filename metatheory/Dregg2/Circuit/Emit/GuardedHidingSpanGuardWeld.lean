/-
# Dregg2.Circuit.Emit.GuardedHidingSpanGuardWeld — MILESTONE 1: the `hGuard` hypothesis of the
hidden-span weld is DISCHARGED from an emitted descriptor + the proven DFA weld.

Since the felt-width cutover of 2026-07-23 the commit leg is the WIDE-BLIND descriptor
`guardedHidingSpanWideBlindDesc` (the SOLE emitted hidden-span descriptor; the narrow
single-blinding-felt M0 descriptor was DELETED — see the `GuardedHidingSpanEmit` header).

## The gap this closes (exact)

`GuardedHidingSpanWideBlindRefine.guardedHidingSpanWideBlind_refines_parse` carries the guard
obligation `derives s g = true` as the PLAINLY-NAMED hypothesis `hGuard`, because no
table-as-input `Satisfied2 ⟹ classify` refinement general over an arbitrary guard existed (the
emitted routing descriptors hardcode a per-automaton interpolant —
`DfaRoutingEmit`/`DfaRoutingGeneralEmit`; the per-automaton refinement is
`DfaRoutingRefine.dfaRouting_refines_classify:322`). The named connection point was
already proven: `Dregg2.Crypto.DfaEncodingWeld.weld_matches` (`DfaEncodingWeld.lean:147`) — the
`classify ⟺ Matches` transport (via `air_finalState_decides_matches:165` on the crypto-bound
side).

## What is AUTHORED here vs what was ALREADY PROVEN

ALREADY PROVEN (imported, untouched): `DfaEncodingWeld.weld_matches` / `airOf` (the encoding
transport), `Deriv.PredRE.tableDfa_faithful` + `correctness` (`derives ⟺ Matches`),
`DfaAcceptanceAir.lastNext_eq_classifyFrom`, and the wide-blind refinement
(`guardedHidingSpanWideBlind_commit_binds`, `parse_exists_distinct_holes` weld).

AUTHORED here (+ `DfaRoutingTableEmit.lean`, the general table-as-input routing refinement):

  * `classifyFrom_transport_runLocal` / `weld_matches_runLocal` — the RUN-LOCAL sharpening of the
    weld: the decode left-inverses are needed only on the states/symbols the run actually visits,
    not globally. This ELIMINATES (for any concrete instance) the DfaEncodingWeld residual "an
    injective global `encS : PredRE → ℕ` numbering" — the demo below fires with a 2-line
    constructor-shape `encS`, no serialization subproject.
  * `guardLeg_forces_derives` — THE DISCHARGE: a trace satisfying the emitted table-as-input
    routing descriptor (`tableRoutingDesc`, table = the guard-DFA's step graph), whose public
    `final_state` lands in the accept set, FORCES `derives s g = true` for the word `s` the leg
    read — welded through the transport + `tableDfa_faithful` + `correctness`. A twin
    `guardLeg_forces_derives_via_weld_matches` routes VERBATIM through the named connection point
    `DfaEncodingWeld.weld_matches` (global-inverse interface).
  * `guardedHidingSpan_refines_parse_grounded` — the keystone WITHOUT `hGuard`, over the
    WIDE-BLIND descriptor: its guard obligation is derived from the routing leg's
    `Satisfied2Public` + the weld, and the wide-blind descriptor's own `guard_table_commitment`
    lanes (PI[16..23], pinned by `guardPins`) are bound (mod `p`, the deployed pin width) to the
    WIDE commitment `guardTableCommit8 absorb tbl` of the very table that forced the guard.

## What is FORCED vs what stays NAMED (read this before citing the theorem)

FORCED by emitted descriptors (+ the proven welds): the wide-blind commitment relation and
binding (`guardedHidingSpanWideBlind_commit_binds`, unchanged); `final_state = classify(table,
word-read)` for the routing leg (general over the table — `tableRouting_refines_classify`, no
terminal-step hypothesis, no grid envelope); and therefore `derives s g = true` — the `hGuard`
is GONE as an assumption on the guard verdict.

STILL NAMED (each a hypothesis with its exact role):
  * `hsyms` — the routing trace's symbol column IS the encoded span `s`. The two legs are two
    traces of two descriptors; no single emitted descriptor yet pins the hidden span lanes to
    the routing leg's read column. Closing it = ONE JOINT descriptor whose routing rows read the
    committed span lanes (the M2 target). NOTE this is a TRANSPORT identity, not a semantic
    verdict: the plain refinement's `hGuard` assumed guard-satisfaction itself; `hsyms` only
    names which word was read, and the canary shows a guard-failing span makes the hypothesis
    set UNSATISFIABLE.
  * the `encV` sub-residual, precisely: the tree's proven-injective `Value → ℕ` encoder
    (`Poseidon2Binding.Reference.encV`) has images FAR above `p` (e.g. `encV dataVal` ≈ 1e33), so
    it is NOT wire-faithful as a BabyBear symbol id; no proven injective-below-`p` `Value`
    encoder exists. The run-local interface sidesteps it per-instance (any concrete word admits a
    small local encoder, as the demo shows); a global field-canonical `Value` encoding weld is
    the named residual for span alphabets beyond a fixed finite set.
  * `hfaith` — the table agrees with `derives · g` (exactly `weld_matches`'s own premise;
    discharged CONCRETELY below by the derivative automaton `guardTd`, whose agreement is
    definitional).
  * `hstart`/`hfin`/`hacc`/`hgtc` — public statement-side checks (initial pin = encoded start,
    exposed final in the accept set, `guard_table_commitment` = the wide table commitment);
    `hsmall` — table ids `< p` (wire width); the `ChipTableSoundN` floor and the exact-multiset
    completeness note are inherited from the wide-blind refinement / `DfaRoutingTableEmit`.
  * `guardTableCommit8` is the LEAN-side wide 8-felt table commitment; the Rust
    `compute_table_commitment` (`dfa_routing.rs:336`) is a SINGLE-FELT rolling hash (the ~31-bit
    narrow class) — welding to that narrow object is deliberately NOT done.

Everything above `Satisfied2Public` keeps the standing resolution: the Lean denotation models the
deployed LogUp/AIR; a STARK proves the TRACE; the FRI floor is undischarged.

## Axiom hygiene

No `sorry`, no new axiom; `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Imports
read-only.
-/
import Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine
import Dregg2.Circuit.Emit.DfaRoutingTableEmit
import Dregg2.Crypto.DfaEncodingWeld

namespace Dregg2.Circuit.Emit.GuardedHidingSpanGuardWeld

open Dregg2.Circuit (Assignment)
open Dregg2.Exec (Value)
open Dregg2.Exec.PredAlgebra (Pred)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.Emit.BlindedMembershipWideEmit (wVal wPermOut)
open Dregg2.Circuit.Emit.GuardedHidingSpanEmit (piGUARD)
open Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit
open Dregg2.Circuit.Emit.GuardedHidingSpanRefine
  (m0Template m0_holes_nodup m0_mem wZeroAbsorb)
open Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine
  (guardedHidingSpanWideBlind_commit_binds witTraceW witTfW_chip_sound witTraceW_satisfies)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
  (tableRoutingDesc demoTbl DEMO_NAME demoRoutingDesc routeWitTrace routeWit_satisfies
   row_triple tableRouting_refines_classify SYMBOL PI_INITIAL PI_FINAL)
open Dregg2.Crypto.Deriv (PredRE)
open Dregg2.Crypto.Deriv.PredRE (derives Matches leaf der null correctness tableDfa_faithful)
open Dregg2.Crypto.DfaEncodingWeld (CDfa ADfa airOf weld_matches)
open Dregg2.Crypto.DfaAcceptanceAir (classify classifyFrom classifyFrom_cons classifyFrom_nil)
open Dregg2.Crypto.HandlebarsGuarded
  (GuardedTemplate guardedToGrammar render guardedSafe braceVal dataVal braceP
   leaf_braceP_data)
open Dregg2.Crypto.HandlebarsGuardedUniqueness (noBraceRE containsB)
open Dregg2.Crypto.HandlebarsGuardedParse (parse_exists_distinct_holes)

set_option autoImplicit false

/-! ## §1 — the RUN-LOCAL weld transport.

`DfaEncodingWeld.classifyFrom_transport` consumes GLOBAL decode left-inverses
(`∀ s, decS (encS s) = s`), whose concrete supply is the named "injective `PredRE → ℕ`
numbering" serialization residual. The transport only ever decodes states ALONG THE RUN and
symbols IN THE WORD — so we sharpen it to exactly that, and every concrete instance discharges
its encoding side with a finite, hand-checked local encoder. -/

/-- The states a run visits (start included): `runStates td q w`. -/
def runStates {S Y : Type} (td : CDfa S Y) : S → List Y → List S
  | q, []      => [q]
  | q, a :: as => q :: runStates td (td.step q a) as

/-- The run's final state is among the visited states. -/
theorem runState_mem_runStates {S Y : Type} (td : CDfa S Y) :
    ∀ (w : List Y) (q : S), td.runState q w ∈ runStates td q w
  | [], _ => List.mem_singleton.mpr rfl
  | _ :: as, q => List.mem_cons_of_mem _ (runState_mem_runStates td as (td.step q _))

/-- **`classifyFrom_transport_runLocal`** — `DfaEncodingWeld.classifyFrom_transport` with the
decode left-inverses demanded ONLY on the visited states / read symbols. -/
theorem classifyFrom_transport_runLocal {S Y : Type} (td : CDfa S Y)
    (encS : S → Nat) (decS : Nat → S) (encY : Y → Nat) (decY : Nat → Y) :
    ∀ (w : List Y) (q : S),
      (∀ q' ∈ runStates td q w, decS (encS q') = q') →
      (∀ a ∈ w, decY (encY a) = a) →
      classifyFrom (airOf td encS decS encY decY) (encS q) (w.map encY)
        = encS (td.runState q w)
  | [], _, _, _ => rfl
  | a :: as, q, hS, hY => by
      simp only [List.map_cons, classifyFrom_cons]
      have hstep : (airOf td encS decS encY decY).step (encS q) (encY a)
          = encS (td.step q a) := by
        show encS (td.step (decS (encS q)) (decY (encY a))) = encS (td.step q a)
        rw [hS q (by simp [runStates]), hY a List.mem_cons_self]
      rw [hstep]
      exact classifyFrom_transport_runLocal td encS decS encY decY as (td.step q a)
        (fun q' hq' => hS q' (by simp only [runStates, List.mem_cons]; exact Or.inr hq'))
        (fun b hb => hY b (List.mem_cons_of_mem _ hb))

/-- **`accepts_transport_runLocal`** — word-acceptance transports under run-local inverses. -/
theorem accepts_transport_runLocal {S Y : Type} (td : CDfa S Y)
    (encS : S → Nat) (decS : Nat → S) (encY : Y → Nat) (decY : Nat → Y) (w : List Y)
    (hS : ∀ q ∈ runStates td td.start w, decS (encS q) = q)
    (hY : ∀ a ∈ w, decY (encY a) = a) :
    (airOf td encS decS encY decY).accepts
        (classify (airOf td encS decS encY decY) (w.map encY))
      ↔ td.accepts w := by
  have hcl : classify (airOf td encS decS encY decY) (w.map encY)
      = encS (td.runState td.start w) :=
    classifyFrom_transport_runLocal td encS decS encY decY w td.start hS hY
  rw [hcl]
  show td.accept (decS (encS (td.runState td.start w))) ↔ td.accept (td.runState td.start w)
  rw [hS _ (runState_mem_runStates td w td.start)]

/-- **`weld_matches_runLocal`** — `DfaEncodingWeld.weld_matches` with run-local encoding
hypotheses: the transported table word-decides EXACTLY `Matches · R` on the given word. Chains
the untouched `tableDfa_faithful`. -/
theorem weld_matches_runLocal (td : CDfa PredRE Value) (R : PredRE)
    (encS : PredRE → Nat) (decS : Nat → PredRE) (encY : Value → Nat) (decY : Nat → Value)
    (w : List Value)
    (hS : ∀ q ∈ runStates td td.start w, decS (encS q) = q)
    (hY : ∀ a ∈ w, decY (encY a) = a)
    (hfaith : ∀ w', td.accepts w' ↔ derives w' R = true) :
    (airOf td encS decS encY decY).accepts
        (classify (airOf td encS decS encY decY) (w.map encY))
      ↔ Matches w R := by
  rw [accepts_transport_runLocal td encS decS encY decY w hS hY]
  exact tableDfa_faithful td R hfaith w

/-! ## §2 — THE DISCHARGE: the routing leg + the weld force `derives s g = true`. -/

/-- **`guardLeg_forces_derives`** — the M1 keystone tooth. A trace `t'` satisfying the EMITTED
table-as-input routing descriptor over the guard-DFA's step graph (via the deployed
`Satisfied2Public`), whose symbol column is the encoded span `s` (`hsyms`, the named transport
identity), whose public `initial_state` is the encoded start, and whose exposed public
`final_state` lands in the accept set (`hacc` — the verifier-side accept check), FORCES

    `derives s g = true`

— the exact obligation M0 carried as `hGuard`. Chain: `tableRouting_refines_classify` (the
general table-as-input refinement, `DfaRoutingTableEmit`) ⟶ run-local transport ⟶
`tableDfa_faithful` ⟶ `correctness`. -/
theorem guardLeg_forces_derives
    (g : PredRE) (td : CDfa PredRE Value)
    (encS : PredRE → Nat) (decS : Nat → PredRE) (encY : Value → Nat) (decY : Nat → Value)
    (s : List Value)
    (hS : ∀ q ∈ runStates td td.start s, decS (encS q) = q)
    (hY : ∀ a ∈ s, decY (encY a) = a)
    (hfaith : ∀ w', td.accepts w' ↔ derives w' g = true)
    (tbl : List (List Nat)) (rname : String)
    (htbl : ∀ r ∈ tbl, ∃ s' y', r = [s', y', (airOf td encS decS encY decY).step s' y'])
    (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    {hash' : List ℤ → ℤ} {minit' : ℤ → ℤ} {mfin' : ℤ → ℤ × Nat} {maddrs' : List ℤ}
    {t' : VmTrace}
    (hsat' : Satisfied2Public hash' (tableRoutingDesc rname tbl) minit' mfin' maddrs' t')
    (hne' : t'.rows ≠ [])
    (hstart : t'.pub PI_INITIAL = Int.ofNat (encS td.start))
    (hq0 : encS td.start < 2013265921)
    (fN : ℕ) (hfin : t'.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921)
    (hacc : td.accept (decS fN))
    (hsyms : t'.rows.map (fun a => a SYMBOL) = (s.map encY).map Int.ofNat) :
    derives s g = true := by
  obtain ⟨_, hclass⟩ := tableRouting_refines_classify (airOf td encS decS encY decY)
    htbl hsmall hsat' hne' (encS td.start) hstart hq0 fN hfin hfN
  -- the word the leg read IS the encoded span
  have hws : t'.rows.map (fun a => (a SYMBOL).toNat) = s.map encY := by
    have h := congrArg (List.map Int.toNat) hsyms
    simpa [List.map_map, Function.comp_def] using h
  rw [hws] at hclass
  -- classify of the encoded span = the exposed accepted final id
  have hcls : classify (airOf td encS decS encY decY) (s.map encY) = fN := by
    have hc : classify (airOf td encS decS encY decY) (s.map encY)
        = classifyFrom (airOf td encS decS encY decY) (encS td.start) (s.map encY) := rfl
    rw [hc, ← hclass]
  have haccepts : (airOf td encS decS encY decY).accepts
      (classify (airOf td encS decS encY decY) (s.map encY)) := by
    show td.accept (decS (classify (airOf td encS decS encY decY) (s.map encY)))
    rw [hcls]
    exact hacc
  have hM : Matches s g :=
    (weld_matches_runLocal td g encS decS encY decY s hS hY hfaith).mp haccepts
  exact (correctness s g).mpr hM

/-- **`guardLeg_forces_derives_via_weld_matches`** — the same discharge routed VERBATIM through
the named connection point `DfaEncodingWeld.weld_matches` (global decode-inverse interface: this
is exactly the shape whose `encS` supply is the DfaEncodingWeld serialization residual; the
run-local form above eliminates it per-instance). -/
theorem guardLeg_forces_derives_via_weld_matches
    (g : PredRE) (td : CDfa PredRE Value)
    (encS : PredRE → Nat) (decS : Nat → PredRE) (encY : Value → Nat) (decY : Nat → Value)
    (s : List Value)
    (hSg : ∀ q, decS (encS q) = q)
    (hYg : ∀ a, decY (encY a) = a)
    (hfaith : ∀ w', td.accepts w' ↔ derives w' g = true)
    (tbl : List (List Nat)) (rname : String)
    (htbl : ∀ r ∈ tbl, ∃ s' y', r = [s', y', (airOf td encS decS encY decY).step s' y'])
    (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    {hash' : List ℤ → ℤ} {minit' : ℤ → ℤ} {mfin' : ℤ → ℤ × Nat} {maddrs' : List ℤ}
    {t' : VmTrace}
    (hsat' : Satisfied2Public hash' (tableRoutingDesc rname tbl) minit' mfin' maddrs' t')
    (hne' : t'.rows ≠ [])
    (hstart : t'.pub PI_INITIAL = Int.ofNat (encS td.start))
    (hq0 : encS td.start < 2013265921)
    (fN : ℕ) (hfin : t'.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921)
    (hacc : td.accept (decS fN))
    (hsyms : t'.rows.map (fun a => a SYMBOL) = (s.map encY).map Int.ofNat) :
    derives s g = true := by
  obtain ⟨_, hclass⟩ := tableRouting_refines_classify (airOf td encS decS encY decY)
    htbl hsmall hsat' hne' (encS td.start) hstart hq0 fN hfin hfN
  have hws : t'.rows.map (fun a => (a SYMBOL).toNat) = s.map encY := by
    have h := congrArg (List.map Int.toNat) hsyms
    simpa [List.map_map, Function.comp_def] using h
  rw [hws] at hclass
  have hcls : classify (airOf td encS decS encY decY) (s.map encY) = fN := by
    have hc : classify (airOf td encS decS encY decY) (s.map encY)
        = classifyFrom (airOf td encS decS encY decY) (encS td.start) (s.map encY) := rfl
    rw [hc, ← hclass]
  have haccepts : (airOf td encS decS encY decY).accepts
      (classify (airOf td encS decS encY decY) (s.map encY)) := by
    show td.accept (decS (classify (airOf td encS decS encY decY) (s.map encY)))
    rw [hcls]
    exact hacc
  -- THE NAMED CONNECTION POINT, applied verbatim:
  have hM : Matches s g :=
    (weld_matches td g encS decS encY decY hSg hYg hfaith s).mp haccepts
  exact (correctness s g).mpr hM

/-! ## §3 — the wide-blind descriptor's guard-identity lanes, pinned to the table commitment. -/

/-- The LEAN-side WIDE 8-felt commitment of a declared transition table (all entries in the
absorb preimage; contrast the Rust single-felt `compute_table_commitment`, the narrow legacy). -/
def guardTableCommit8 (absorb : List ℤ → Digest8) (tbl : List (List Nat)) : Digest8 :=
  absorb (tbl.flatten.map Int.ofNat)

/-- The wide-blind descriptor genuinely carries the `guard_table_commitment` pins (all 8 lanes). -/
theorem mem_guardPin (k : Fin 8) :
    VmConstraint2.base (.piBinding .first (gGUARD k) (piGUARD k))
      ∈ guardedHidingSpanWideBlindDesc.constraints := by
  have hin : VmConstraint2.base (.piBinding .first (gGUARD k) (piGUARD k)) ∈ guardPins := by
    simp only [guardPins, List.mem_map]
    exact ⟨k, List.mem_finRange k, rfl⟩
  simp only [guardedHidingSpanWideBlindDesc, List.append_assoc, List.mem_append, List.mem_cons]
  tauto

/-- A `Satisfied2` witness of the wide-blind descriptor has its guard-identity lane `k` pinned
(mod `p`, the deployed pin width) to the public `guard_table_commitment` PI. -/
theorem guard_lane_pinned
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash guardedHidingSpanWideBlindDesc minit mfin maddrs t) (hne : t.rows ≠ [])
    (k : Fin 8) :
    (envAt t 0).loc (gGUARD k) ≡ t.pub (piGUARD k) [ZMOD 2013265921] := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hrc := hsat.rowConstraints 0 hpos _ (mem_guardPin k)
  exact (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length)
    (gGUARD k) (piGUARD k)).mp hrc

/-! ## §4 — the GROUNDED keystone: the wide-blind weld WITHOUT `hGuard`. -/

/-- Row 0 of a trace (the commit leg's logical row). -/
def row0 (t : VmTrace) : Assignment := (envAt t 0).loc

/-- **`guardedHidingSpan_refines_parse_grounded` — the M1 keystone, over the WIDE-BLIND
descriptor.** The plain refinement statement
(`guardedHidingSpanWideBlind_refines_parse`) with the plainly-named `hGuard` REMOVED: the hole
span's guard obligation is DERIVED from (a) a `Satisfied2Public` witness of the emitted
table-as-input routing descriptor over the guard-DFA's step graph, and (b) the proven encoding
weld — and the wide-blind descriptor's own `guard_table_commitment` lanes are pinned (mod `p`)
to the wide commitment of THAT table, binding the guard identity `g` into the public statement.
Conclusions:

  1. the wide-blind commit binding (unchanged, from `guardedHidingSpanWideBlind_commit_binds` —
     all 5 blinding lanes in the preimage);
  2. `guard_table_commitment` lanes ≡ `guardTableCommit8 absorb tbl` — the published guard
     identity is the commitment of the table that forced the verdict;
  3. `derives s g = true` — FORCED, not assumed;
  4. the parse theorem fires (`parse_exists_distinct_holes`, untouched).

Named hypotheses (the honest floor, itemized in the header): `hsyms` (span↔symbol-column
transport — the M2 joint-descriptor target), `hfaith`, the public checks
`hstart`/`hfin`/`hacc`/`hgtc`, `hsmall`, and the inherited `ChipTableSoundN`. -/
theorem guardedHidingSpan_refines_parse_grounded
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (absorb : List ℤ → Digest8)
    (hChip : ChipTableSoundN (wPermOut absorb) (t.tf .poseidon2))
    (hsat : Satisfied2 hash guardedHidingSpanWideBlindDesc minit mfin maddrs t) (hne : t.rows ≠ [])
    (lit0 lit1 : List Value) (s : List Value) (g : PredRE)
    -- the guard-DFA leg (replaces hGuard):
    (td : CDfa PredRE Value)
    (encS : PredRE → Nat) (decS : Nat → PredRE) (encY : Value → Nat) (decY : Nat → Value)
    (hS : ∀ q ∈ runStates td td.start s, decS (encS q) = q)
    (hY : ∀ a ∈ s, decY (encY a) = a)
    (hfaith : ∀ w', td.accepts w' ↔ derives w' g = true)
    (tbl : List (List Nat)) (rname : String)
    (htbl : ∀ r ∈ tbl, ∃ s' y', r = [s', y', (airOf td encS decS encY decY).step s' y'])
    (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    {hash' : List ℤ → ℤ} {minit' : ℤ → ℤ} {mfin' : ℤ → ℤ × Nat} {maddrs' : List ℤ}
    {t' : VmTrace}
    (hsat' : Satisfied2Public hash' (tableRoutingDesc rname tbl) minit' mfin' maddrs' t')
    (hne' : t'.rows ≠ [])
    (hstart : t'.pub PI_INITIAL = Int.ofNat (encS td.start))
    (hq0 : encS td.start < 2013265921)
    (fN : ℕ) (hfin : t'.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921)
    (hacc : td.accept (decS fN))
    (hsyms : t'.rows.map (fun a => a SYMBOL) = (s.map encY).map Int.ofNat)
    (hgtc : ∀ k : Fin 8, t.pub (piGUARD k) = guardTableCommit8 absorb tbl k) :
    (wVal (row0 t) gHOLE
        = holeCommitWideOf absorb (wVal (row0 t) gDIGEST) (wVal (row0 t) gCT) (bVal (row0 t))
      ∧ wVal (row0 t) gDIGEST = absorb (packSpanW (wVal (row0 t) gSPAN)))
    ∧ (∀ k : Fin 8, wVal (row0 t) gGUARD k ≡ guardTableCommit8 absorb tbl k [ZMOD 2013265921])
    ∧ derives s g = true
    ∧ (∃ d : Nat → List Value, guardedSafe (m0Template lit0 lit1 g) d
         ∧ render (m0Template lit0 lit1 g) d = lit0 ++ s ++ lit1) := by
  have hGuard : derives s g = true :=
    guardLeg_forces_derives g td encS decS encY decY s hS hY hfaith tbl rname htbl hsmall
      hsat' hne' hstart hq0 fN hfin hfN hacc hsyms
  have hbind := guardedHidingSpanWideBlind_commit_binds absorb hChip hsat hne
  refine ⟨⟨hbind.2, hbind.1⟩, ?_, hGuard, ?_⟩
  · intro k
    have hpin := guard_lane_pinned hsat hne k
    rw [hgtc k] at hpin
    exact hpin
  · exact parse_exists_distinct_holes (m0Template lit0 lit1 g) (m0_holes_nodup lit0 lit1 g)
      (lit0 ++ s ++ lit1) (m0_mem lit0 lit1 s g hGuard)

/-! ## §5 — CANARY A: a guard-FAILING span makes the routing-leg hypothesis set UNSATISFIABLE.
The discharge is load-bearing: no `Satisfied2Public` witness can present a span violating its
guard (given the same weld data), because the descriptor would force `derives s g = true`. -/

theorem guardFailing_span_refused
    (g : PredRE) (td : CDfa PredRE Value)
    (encS : PredRE → Nat) (decS : Nat → PredRE) (encY : Value → Nat) (decY : Nat → Value)
    (s : List Value)
    (hS : ∀ q ∈ runStates td td.start s, decS (encS q) = q)
    (hY : ∀ a ∈ s, decY (encY a) = a)
    (hfaith : ∀ w', td.accepts w' ↔ derives w' g = true)
    (tbl : List (List Nat)) (rname : String)
    (htbl : ∀ r ∈ tbl, ∃ s' y', r = [s', y', (airOf td encS decS encY decY).step s' y'])
    (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    {hash' : List ℤ → ℤ} {minit' : ℤ → ℤ} {mfin' : ℤ → ℤ × Nat} {maddrs' : List ℤ}
    {t' : VmTrace}
    (hne' : t'.rows ≠ [])
    (hstart : t'.pub PI_INITIAL = Int.ofNat (encS td.start))
    (hq0 : encS td.start < 2013265921)
    (fN : ℕ) (hfin : t'.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921)
    (hacc : td.accept (decS fN))
    (hsyms : t'.rows.map (fun a => a SYMBOL) = (s.map encY).map Int.ofNat)
    (hbad : derives s g = false) :
    ¬ Satisfied2Public hash' (tableRoutingDesc rname tbl) minit' mfin' maddrs' t' := by
  intro hsat'
  have hforced := guardLeg_forces_derives g td encS decS encY decY s hS hY hfaith tbl rname
    htbl hsmall hsat' hne' hstart hq0 fN hfin hfN hacc hsyms
  rw [hbad] at hforced
  exact absurd hforced (by decide)

/-! ## §6 — CANARY B: a mutated `guard_table_commitment` breaks the binding.

(i) the wide commitment DISCRIMINATES tables (a mutated table has a different commitment under
the M0 demo absorb), and (ii) a public `guard_table_commitment` carrying a DIFFERENT table's
commitment refuses the `hgtc` binding for the real table. Plus (iii): forging the M0 witness's
guard PI lane against its trace lane PROVABLY fails `Satisfied2` (the pin bites). -/

-- (i) discrimination: the mutated table [[0,1,0]] commits differently from [[0,1,1]].
#guard decide (guardTableCommit8 Dregg2.Circuit.Emit.GuardedHidingSpanEmit.demoAbsorb [[0, 1, 1]]
  ≠ guardTableCommit8 Dregg2.Circuit.Emit.GuardedHidingSpanEmit.demoAbsorb [[0, 1, 0]])

/-- (ii) a `guard_table_commitment` equal to a DIFFERENT table's commitment cannot ALSO satisfy
the binding for the real table (lane-wise refusal). -/
theorem mutated_commitment_refused (absorb : List ℤ → Digest8)
    (tbl tbl' : List (List Nat)) {t : VmTrace} (k : Fin 8)
    (hdisc : guardTableCommit8 absorb tbl k ≠ guardTableCommit8 absorb tbl' k)
    (hgtc : ∀ j : Fin 8, t.pub (piGUARD j) = guardTableCommit8 absorb tbl j) :
    t.pub (piGUARD k) ≠ guardTableCommit8 absorb tbl' k := by
  rw [hgtc k]
  exact hdisc

/-- (iii) the wide-blind witness with a FORGED `guard_table_commitment` PI (lane 0 flipped to `1`
while the genuine guard lane is `0`): the guard pin (`guardPins`, genuinely in the descriptor —
`mem_guardPin`) refuses it. -/
def mutGuardTrace : VmTrace :=
  { rows := [Dregg2.Circuit.Emit.GuardedHidingSpanRefine.wRow]
  , pub := fun i => if i = piGUARD 0 then 1 else 0
  , tf := Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine.wTfW }

theorem mutGuard_not_satisfied :
    ¬ Satisfied2 Dregg2.Circuit.Emit.GuardedHidingSpanRefine.hash0 guardedHidingSpanWideBlindDesc
        (fun _ => 0) (fun _ => (0, 0)) [] mutGuardTrace := by
  intro h
  have hmod := guard_lane_pinned h (List.cons_ne_nil _ _) 0
  have he : (envAt mutGuardTrace 0).loc (gGUARD 0) = 0 := rfl
  have hp : mutGuardTrace.pub (piGUARD 0) = 1 := rfl
  rw [he, hp] at hmod
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hmod.symm
  omega

/-! ## §7 — NON-VACUITY: a concrete accepting instance FIRES the grounded theorem.

The guard is the REAL `noBraceRE` (`neg (any* ⬝ brace ⬝ any*)`); the automaton is the DERIVATIVE
automaton itself (`step := der`, `accept := null` — its agreement with `derives` is
DEFINITIONAL, so `hfaith` is discharged, not assumed); the hidden span is `[dataVal]`
(brace-free); the routing leg is the byte-pinned `demoRoutingDesc` instance with its
`routeWit_satisfies` witness (`DfaRoutingTableEmit`); the encodings are a 2-state / 2-symbol
LOCAL encoder (run-local weld — no global `PredRE → ℕ` numbering consumed). The commit leg
reuses the wide-blind witness (`witTraceW_satisfies`, `witTfW_chip_sound`) unchanged. -/

namespace Demo

/-- The derivative state after reading `dataVal` from `noBraceRE`. -/
def q1 : PredRE := der dataVal noBraceRE

/-- `any = sym tt` fires on `dataVal` (the `tt` leaf admits every frame). -/
theorem leaf_tt_data : leaf Pred.tt dataVal = true := by
  simp [Dregg2.Crypto.Deriv.PredRE.leaf, Pred.eval]

/-- `q1` computed symbolically: `neg (alt ((ε⬝any*)⬝(brace⬝any*)) (∅⬝any*))` — its head is
`neg (alt …)`, DISTINCT from `noBraceRE`'s head `neg (cat …)`, which is what the local state
encoder discriminates on. -/
theorem q1_eq : q1 = .neg (.alt
    (.cat (.cat .ε (.star PredRE.any)) (.cat (.sym braceP) (.star PredRE.any)))
    (.cat PredRE.bot (.star PredRE.any))) := by
  have htt : Pred.tt.eval (PredRE.symbolOld dataVal) dataVal = true := leaf_tt_data
  have hbr : braceP.eval (PredRE.symbolOld dataVal) dataVal = false := leaf_braceP_data
  simp only [q1, noBraceRE, containsB]
  simp
  constructor
  · simp [htt]
  · simp [hbr]

/-- The LOCAL state encoder: constructor-shape discrimination (`neg∘cat ↦ 0`, else `1`). NO
global injectivity, NO `PredRE` decidable equality — the run-local weld needs only the two
visited states to round-trip. -/
def encSd : PredRE → ℕ
  | .neg (.cat _ _) => 0
  | _ => 1

/-- The local state decoder. -/
def decSd : ℕ → PredRE := fun n => if n = 0 then noBraceRE else q1

theorem encSd_start : encSd noBraceRE = 0 := rfl

theorem encSd_q1 : encSd q1 = 1 := by rw [q1_eq]; rfl

/-- The LOCAL symbol encoder (`dataVal ↦ 1`, everything else `0`) — small ids, wire-faithful
below `p` (contrast `encV dataVal` ≈ 1e33, the named encV sub-residual). -/
def encYd : Value → ℕ
  | .record [(_, .sym n)] => n
  | _ => 0

/-- The local symbol decoder. -/
def decYd : ℕ → Value := fun n => if n = 1 then dataVal else braceVal

theorem encYd_data : encYd dataVal = 1 := rfl

/-- **The derivative automaton of `noBraceRE`** as the compiler-side table: `step := der`,
`accept := null`. Its language agreement with `derives` is definitional (`run_null`). -/
def guardTd : CDfa PredRE Value :=
  { step := fun s a => der a s, start := noBraceRE, accept := fun s => null s = true }

theorem guardTd_run_null : ∀ (w : List Value) (q : PredRE),
    null (guardTd.runState q w) = derives w q
  | [], _ => rfl
  | a :: as, q => guardTd_run_null as (der a q)

/-- `hfaith` DISCHARGED (not assumed): the derivative automaton agrees with `derives · noBraceRE`
on every word. -/
theorem guardTd_faith : ∀ w, guardTd.accepts w ↔ derives w noBraceRE = true := by
  intro w
  show null (guardTd.runState noBraceRE w) = true ↔ _
  rw [guardTd_run_null]

/-- The reached state after the brace-free span ACCEPTS (`null q1 = true`). -/
theorem null_q1 : null q1 = true := by rw [q1_eq]; rfl

/-- Run-local state round-trip on the visited states `[noBraceRE, q1]`. -/
theorem hS_demo : ∀ q ∈ runStates guardTd guardTd.start [dataVal], decSd (encSd q) = q := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · rfl
  · have hq1 : q = q1 := by
      simp only [runStates, List.mem_cons, List.not_mem_nil, or_false] at hq'
      exact hq'
    subst hq1
    rw [encSd_q1]
    rfl

/-- Run-local symbol round-trip on the read word `[dataVal]`. -/
theorem hY_demo : ∀ a ∈ [dataVal], decYd (encYd a) = a := by
  intro a ha
  rw [List.mem_singleton.mp ha]
  rfl

/-- The transported step on the encoded ids: `0 --1--> 1` — exactly the pinned `demoTbl` row. -/
theorem airOf_step_demo : (airOf guardTd encSd decSd encYd decYd).step 0 1 = 1 := by
  show encSd (guardTd.step (decSd 0) (decYd 1)) = 1
  show encSd (der dataVal noBraceRE) = 1
  exact encSd_q1

/-- The pinned demo table IS the transported step graph. -/
theorem htbl_demo : ∀ r ∈ demoTbl,
    ∃ s' y', r = [s', y', (airOf guardTd encSd decSd encYd decYd).step s' y'] := by
  intro r hr
  simp only [demoTbl, List.mem_singleton] at hr
  exact ⟨0, 1, by rw [airOf_step_demo]; exact hr⟩

/-- The exposed final id `1` decodes to `q1`, which ACCEPTS. -/
theorem hacc_demo : guardTd.accept (decSd 1) := by
  show null q1 = true
  exact null_q1

/-- **THE GROUNDED THEOREM FIRES** on the concrete pair of witnesses — the wide-blind witness
trace (`witTraceW_satisfies`, the emitted commit descriptor) and the routing witness
(`routeWit_satisfies`, the byte-pinned table-as-input instance). The guard verdict
`derives [dataVal] noBraceRE = true` is PRODUCED by the theorem (conclusion 3) — not assumed —
and the parse theorem fires on the recovered span (conclusion 4). -/
theorem grounded_fires :
    derives [dataVal] noBraceRE = true
    ∧ (∃ d : Nat → List Value,
        guardedSafe (m0Template [dataVal] [dataVal] noBraceRE) d
        ∧ render (m0Template [dataVal] [dataVal] noBraceRE) d
            = [dataVal] ++ [dataVal] ++ [dataVal]) := by
  have h := guardedHidingSpan_refines_parse_grounded
    wZeroAbsorb witTfW_chip_sound witTraceW_satisfies (List.cons_ne_nil _ _)
    [dataVal] [dataVal] [dataVal] noBraceRE
    guardTd encSd decSd encYd decYd hS_demo hY_demo guardTd_faith
    demoTbl DEMO_NAME htbl_demo (by decide)
    routeWit_satisfies (List.cons_ne_nil _ _)
    rfl (by decide)
    1 rfl (by decide)
    hacc_demo
    rfl
    (fun _ => rfl)
  exact ⟨h.2.2.1, h.2.2.2⟩

-- Non-vacuity pins (compiled evaluation): the guard verdict the theorem produces is REAL —
-- the matcher accepts the brace-free span and rejects a brace.
#guard derives [dataVal] noBraceRE
#guard ! derives [braceVal] noBraceRE
#guard encYd dataVal == 1

/-! ### The brace-span refusal, CONCRETE: a routing trace reading the brace symbol id (`0`)
cannot satisfy the pinned instance — its triple is not a declared table row. -/

/-- A trace claiming to read the BRACE symbol (`symbol id 0`): `(0, 0, 1)`. -/
def braceRow : Assignment := fun c => if c = 2 then 1 else 0

def braceTrace : VmTrace :=
  { rows := [braceRow]
  , pub := Dregg2.Circuit.Emit.DfaRoutingTableEmit.wPub
  , tf := Dregg2.Circuit.Emit.DfaRoutingTableEmit.wTf }

/-- **The brace-reading trace PROVABLY fails `Satisfied2Public`** — the table-as-input lookup
refuses the undeclared triple `(0, 0, 1)`. The guard tooth bites at the descriptor level. -/
theorem braceTrace_refused :
    ¬ Satisfied2Public Dregg2.Circuit.Emit.DfaRoutingTableEmit.hash0 demoRoutingDesc
        (fun _ => 0) (fun _ => (0, 0)) [] braceTrace := by
  intro h
  have hm := row_triple h (i := 0) (by decide)
  revert hm
  decide

end Demo

/-! ## §8 — axiom tripwires (the keystones + the firing demo). -/

#assert_axioms classifyFrom_transport_runLocal
#assert_axioms weld_matches_runLocal
#assert_axioms guardLeg_forces_derives
#assert_axioms guardLeg_forces_derives_via_weld_matches
#assert_axioms guardedHidingSpan_refines_parse_grounded
#assert_axioms guardFailing_span_refused
#assert_axioms mutated_commitment_refused
#assert_axioms mutGuard_not_satisfied
#assert_axioms Demo.guardTd_faith
#assert_axioms Demo.grounded_fires
#assert_axioms Demo.braceTrace_refused

end Dregg2.Circuit.Emit.GuardedHidingSpanGuardWeld
