/-
# Dregg2.Circuit.Emit.DfaRoutingRung2 — the RUNG-2 discharge of the terminal-step obligation for the
emitted DFA-routing descriptor (`dfaRoutingDesc`), via the Poseidon2 route-commitment binding.

## What this file IS

`DfaRoutingRefine.lean` (RUNG 1) proves the bridge `Satisfied2 ∧ nonempty ∧ hterm ⟹ genuine run ∧
final = classify(input)`, where `hterm` is the terminal-step obligation: the LAST row is also a
genuine transition. The deployed STARK divides every per-row constraint by the TRANSITION zerofier
(`circuit/src/stark.rs`), so the toggle gate is NOT enforced on the last row — `hterm` is exactly the
gap the gate lowering leaves. RUNG 2 DISCHARGES `hterm` from the running-hash route-commitment
binding, so the top-level conclusion `final = classify(input)` rides the standard Poseidon2 CR
carrier instead of an unenforced witness column.

## Why an anchor is genuinely needed (this is NOT laundering)

Unconditional `Satisfied2 ⟹ final = classify` is FALSE, and provably so: a prover may set the last
row's `next` to ANY value, compute the matching entry/running hashes, and expose that as
`final_state` / `route_commitment`. Every gate (divided by the zerofier) still holds on the non-last
rows, both chip lookups still hold on every row, and B2/B3 pin the fake values — so the trace
`Satisfied2`, yet `final ≠ classify(input)` (`rung2_needs_anchor`, §6: the honest `witTrace` with its
last edge flipped `Satisfied2`s with a wrong final). The soundness of "classified to S" therefore
pivots on the DISCLOSED `route_commitment` being the honest commitment of a genuine run — which is
what the constitution/registry anchor supplies, and what the CR binding converts into `hterm`.

## The discharge (the route-commitment binding, `DfaAcceptanceAir`)

Instantiate `Digest = State = Sym = ℤ`, with the Poseidon2 primitives realized as the descriptor's
own `hash` (`compress a b := hash [a,b]`, `compressN l := hash l` — `dfaPrims`). Against a SOUND chip
table (`ChipTableSound hash` — the chip-AIR faithfulness carrier, `chip_lookup_sound`), the entry /
running lookups of `Satisfied2` force, ON EVERY ROW (lookups are not divided by the zerofier):

  * entry:   `entry_hashᵢ  = hash [currentᵢ, symbolᵢ, nextᵢ, zero_laneᵢ]`   (C1, `compressN`)
  * running: `running_i    = hash [accᵢ, entry_hashᵢ]`                      (C3, `compress`)

with the copy-forward window + seed pin threading `accᵢ`, so the last `running` column is the
`runningFold tableCommitment (entryHashes …)` (`lastRunning_eq_fold`) and B3 pins it to the public
`route_commitment`. Given the CR carrier `CollisionFree (dfaPrims hash)` and a GENUINE reference run
`g` (full `DfaAcceptanceAir.Satisfies`) with the SAME `tableCommitment` / `route_commitment` / length
— the honest anchor — `fold_inj` forces `entryHashes t = entryHashes g`, hence (by `compressN_inj` on
the last entry-hash, using the ALL-ROWS entry lookup) the last `(current, symbol, next)` triple of
`t` equals `g`'s genuine last triple, so `next_last = step(current_last, symbol_last)` — exactly
`hterm`. Feeding it to RUNG 1's `dfaRouting_refines_classify` yields `final = classify(input)`
unconditionally on `hterm`.

## Axiom hygiene / non-vacuity

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the CR carrier `CollisionFree`, the
chip-soundness carrier `ChipTableSound`, and — under the field-faithful mod-`p` denotation — the two
range-check envelopes (`DfaTraceCanon` from Rung 1, `DfaChainCanon` for the running-hash spine,
lifting the mod-`p` seed/copy-forward/route pins to the ℤ equalities the re-hashing fold needs) ride
as NAMED hypotheses, never as Lean axioms, and are jointly inhabited (`refWitness_fires`, over a
reference hash both injective and canonical at the witness digests). §6 exhibits a
concrete satisfying witness (a genuine 2-row toggle run over a REAL injective `hash`, with the CR
carrier discharged from injectivity — `dfaPrims`-`CollisionFree` is inhabited) whose Rung-2 conclusion
FIRES with the true classification, and the cheating trace whose last edge is flipped, which
`Satisfied2`s but breaks the anchor — so the anchor is a real filter, not `True`. NEW file; imports
read-only.
-/
import Dregg2.Circuit.Emit.DfaRoutingRefine

namespace Dregg2.Circuit.Emit.DfaRoutingRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.DfaRoutingEmit
open Dregg2.Circuit.Emit.DfaRoutingRefine
open Dregg2.Circuit.ChipNarrowLookup (narrowTable chip_lookup_narrow_sound_of_wide_table)
open Dregg2.Crypto (CryptoPrimitives)
open Dregg2.Crypto.DfaAcceptanceAir
  (TableDfa Row classify classifyFrom symbols Satisfies Continuous Accumulates CollisionFree
   runningFold entryHashes entryHashOf lastRunning_eq_fold fold_inj route_commitment_binds_trace)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

set_option autoImplicit false

universe u

/-! ## §1 — The Poseidon2 primitives realized as the descriptor's own `hash`. -/

/-- Digest-polymorphic algebraic primitives. At the descriptor's integer specialization,
the abstract operations use its row `hash : List ℤ → ℤ`: `compress a b := hash [a,b]` (the arity-2 `hash_2_to_1` the running-hash
chip lookup binds) and `compressN l := hash l` (the sponge the entry-hash chip lookup binds). The
Pedersen/nullifier carriers are the trivial witnesses (unused by the DFA-routing binding). Marked
`@[reducible]` so the abstract-Poseidon denotations of `DfaAcceptanceAir` compute to `hash`-shaped
equations; forced via `letI` everywhere (the tree also registers a global `CryptoPrimitives Int`). -/
@[reducible] def dfaPrims {Digest : Type u} [AddCommGroup Digest]
    (hash : List Digest → Digest) : CryptoPrimitives Digest where
  compress a b := hash [a, b]
  compressN l := hash l
  collisionHard := True
  commit _ _ := 0
  commit_hom := by intro v w r s; simp
  binding := True
  nullifier := id
  unlinkable := True

/-- Algebraic framework lemma, polymorphic in the digest type. An injective list
encoding supplies the ideal `CollisionFree` laws; this is not a deployed finite-field
hash assumption. The concrete unbounded reference encoding below proves its own
injectivity. Deployed route binding uses an explicit collision alternative. -/
theorem collisionFree_of_injective {Digest : Type u} [AddCommGroup Digest]
    {hash : List Digest → Digest} (hinj : Function.Injective hash) :
    @CollisionFree Digest _ (dfaPrims hash) :=
  letI := dfaPrims hash
  { compress_pair_inj := fun a b c d h => by
      have hlist : [a, b] = [c, d] := hinj h
      injection hlist with h1 h2
      injection h2 with h3 _
      exact ⟨h1, h3⟩
    compressN_inj := fun _ _ h => hinj h }

/-! ## §2 — The two chip lookups + the acc pins are genuinely present in `dfaRoutingDesc`. -/

theorem mem_entryHashLookup : entryHashLookup ∈ dfaRoutingDesc.constraints := by
  simp only [dfaRoutingDesc]
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

theorem mem_runningHashLookup : runningHashLookup ∈ dfaRoutingDesc.constraints := by
  simp only [dfaRoutingDesc]
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

theorem mem_copyForwardWindow : copyForwardWindow ∈ dfaRoutingDesc.constraints := by
  simp only [dfaRoutingDesc]
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

theorem mem_seedAccPin :
    VmConstraint2.base (.piBinding .first ACC PI_TABLE) ∈ dfaRoutingDesc.constraints := by
  show seedAccPin ∈ dfaRoutingDesc.constraints
  simp only [dfaRoutingDesc]
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

theorem mem_b3RoutePin :
    VmConstraint2.base (.piBinding .last RUNNING_HASH PI_ROUTE) ∈ dfaRoutingDesc.constraints := by
  show b3RoutePin ∈ dfaRoutingDesc.constraints
  simp only [dfaRoutingDesc]
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-! ## §3 — Reading the C1 (entry) / C3 (running) hash equations off `Satisfied2` — on EVERY row.

The two chip lookups are `.lookup`s, NOT gates, so `Satisfied2` enforces them on the LAST row too
(the transition-zerofier never divides a lookup). Against a SOUND chip table they carry the hash
equation (`chip_lookup_sound`, the deployed 85%-lever). -/

section Extract
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t)
variable (hchip : ChipTableSound hash (t.tf .poseidon2))
variable (hwire : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2))

include hsat hchip hwire

/-- **C1 (entry-hash), every row.** The entry-hash chip lookup forces
`entry_hashᵢ = hash [currentᵢ, symbolᵢ, nextᵢ, zero_laneᵢ]`. -/
theorem entry_eq {i : Nat} (hi : i < t.rows.length) :
    (t.rows[i]'hi) ENTRY_HASH
      = hash [(t.rows[i]'hi) CURRENT, (t.rows[i]'hi) SYMBOL, (t.rows[i]'hi) NEXT,
              (t.rows[i]'hi) ZERO_LANE] := by
  have hrc := hsat.rowConstraints i hi _ mem_entryHashLookup
  have hmem : (chipLookupTupleNarrow [.var CURRENT, .var SYMBOL, .var NEXT, .var ZERO_LANE]
      ENTRY_HASH).map (·.eval (t.rows[i]'hi)) ∈ narrowTable (t.tf .poseidon2) := by
    have hl : (envAt t i).loc = t.rows[i]'hi := envAt_loc hi
    have h0 : (chipLookupTupleNarrow [.var CURRENT, .var SYMBOL, .var NEXT, .var ZERO_LANE]
        ENTRY_HASH).map (·.eval (t.rows[i]'hi)) ∈ t.tf poseidon2narrow := by
      simpa only [VmConstraint2.holdsAt, entryHashLookup, Lookup.holdsAt, hl] using hrc
    rwa [hwire] at h0
  have h := chip_lookup_narrow_sound_of_wide_table hash (t.tf .poseidon2) hchip (t.rows[i]'hi)
    [.var CURRENT, .var SYMBOL, .var NEXT, .var ZERO_LANE] ENTRY_HASH
    (by decide) hmem
  simpa only [List.map_cons, List.map_nil, EmittedExpr.eval] using h

/-- **C3 (running-hash), every row.** The running-hash chip lookup forces
`running_i = hash [accᵢ, entry_hashᵢ]`. -/
theorem running_eq {i : Nat} (hi : i < t.rows.length) :
    (t.rows[i]'hi) RUNNING_HASH = hash [(t.rows[i]'hi) ACC, (t.rows[i]'hi) ENTRY_HASH] := by
  have hrc := hsat.rowConstraints i hi _ mem_runningHashLookup
  have hmem : (chipLookupTupleNarrow [.var ACC, .var ENTRY_HASH]
      RUNNING_HASH).map (·.eval (t.rows[i]'hi)) ∈ narrowTable (t.tf .poseidon2) := by
    have hl : (envAt t i).loc = t.rows[i]'hi := envAt_loc hi
    have h0 : (chipLookupTupleNarrow [.var ACC, .var ENTRY_HASH]
        RUNNING_HASH).map (·.eval (t.rows[i]'hi)) ∈ t.tf poseidon2narrow := by
      simpa only [VmConstraint2.holdsAt, runningHashLookup, Lookup.holdsAt, hl] using hrc
    rwa [hwire] at h0
  have h := chip_lookup_narrow_sound_of_wide_table hash (t.tf .poseidon2) hchip (t.rows[i]'hi)
    [.var ACC, .var ENTRY_HASH] RUNNING_HASH (by decide) hmem
  simpa only [List.map_cons, List.map_nil, EmittedExpr.eval] using h

end Extract

/-! ## §4 — `Accumulates` of the read run from the running-hash chain (the model's own predicate). -/

/-- If every row's running hash is `hash [accᵢ, entryᵢ]` (C3) and consecutive accumulators
copy-forward (`accᵢ₊₁ = runningᵢ`), the read `Row` list `Accumulates` in `DfaAcceptanceAir`'s sense
(each later `running` extends the previous by the row's entry hash). Induction on the rows, mirroring
`DfaRoutingRefine.continuous_map`. -/
theorem accumulates_map (hash : List ℤ → ℤ) : ∀ (l : List Assignment),
    (∀ i (_ : i < l.length), l[i] RUNNING_HASH = hash [l[i] ACC, l[i] ENTRY_HASH]) →
    (∀ i (_ : i + 1 < l.length), l[i + 1] ACC = l[i] RUNNING_HASH) →
    @Accumulates ℤ ℤ ℤ _ (dfaPrims hash) (l.map mkRow)
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: rest, hrun, hcf => by
      letI := dfaPrims hash
      refine ⟨?_, accumulates_map hash (b :: rest) (fun i hi => ?_) (fun i hi => ?_)⟩
      · show (mkRow b).running = hash [(mkRow a).running, (mkRow b).entryHash]
        have hr := hrun 1 (by simp only [List.length_cons]; omega)
        have hc := hcf 0 (by simp only [List.length_cons]; omega)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero, mkRow] at hr hc ⊢
        rw [hc] at hr; exact hr
      · have hh := hrun (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
        simpa using hh
      · have hh := hcf (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
        simpa using hh

/-! ## §4.5 — the chain canonicality envelope.

Under the field-faithful mod-`p` denotation the seed pin / copy-forward window / B3 route pin bind
only congruences; the running-hash spine RE-HASHES each digest, so a bare congruence cannot thread
through the abstract `hash`. The deployed range-check invariant on the spine cells + the two bound
public inputs is what lifts them to the genuine ℤ equalities the fold argument needs. Inhabited
concretely in §7 (`wtTrace_chainCanon` over the reference hash), so the envelope is non-vacuous. -/

/-- **The chain canonicality envelope** — the running-hash spine cells (`ACC`, `RUNNING_HASH`) are
canonical field cells (`0 ≤ · < p`) on every row, and so are the two bound public inputs
(`pi[table_commitment]`, `pi[route_commitment]`). -/
def DfaChainCanon (t : VmTrace) : Prop :=
  (∀ i, (hi : i < t.rows.length) →
      (0 ≤ (t.rows[i]'hi) ACC ∧ (t.rows[i]'hi) ACC < 2013265921)
      ∧ (0 ≤ (t.rows[i]'hi) RUNNING_HASH ∧ (t.rows[i]'hi) RUNNING_HASH < 2013265921))
  ∧ (0 ≤ t.pub PI_TABLE ∧ t.pub PI_TABLE < 2013265921)
  ∧ (0 ≤ t.pub PI_ROUTE ∧ t.pub PI_ROUTE < 2013265921)

/-! ## §5 — THE RUNG-2 DISCHARGE. -/

/-- **`dfaRouting_rung2` — the terminal-step obligation `hterm` is DISCHARGED by the route-commitment
binding.**

A trace `t` that `Satisfied2`s the emitted `dfaRoutingDesc`, is non-empty, rides a SOUND Poseidon2
chip table (`hchip`, the chip-AIR faithfulness carrier), the CR carrier `cf : CollisionFree`, and — as
the honest route-commitment anchor — a GENUINE reference run `g` (a full `DfaAcceptanceAir.Satisfies`
over the pinned toggle DFA, encodings `id`, with the SAME `tableCommitment` and public
`routeCommitment` and the same length) has its exposed public `final_state` equal to `classify(input)`
— WITHOUT `hterm` as a hypothesis.

The binding fires: both traces' last `running` columns are the SAME `runningFold tableCommitment
(entryHashes …)` (pinned to the public `routeCommitment` by B3), so `fold_inj` forces
`entryHashes t = entryHashes g`; the ALL-ROWS entry lookup + `compressN`-CR (`cf`) then force the last
`(current, symbol, next)` triple of `t` to equal `g`'s genuine last triple, so `next_last =
step(current_last, symbol_last)` — exactly `hterm`. Feeding it to RUNG 1's
`dfaRouting_refines_classify` gives the classification. -/
theorem dfaRouting_rung2 {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace}
    (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (hcanon : DfaTraceCanon t)
    (hchain : DfaChainCanon t)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2))
    (cf : @CollisionFree ℤ _ (dfaPrims hash))
    (gRows : List (Row ℤ ℤ ℤ))
    (hg : @Satisfies ℤ ℤ ℤ _ (dfaPrims hash) (pinnedDfa (t.pub PI_INITIAL)) id id
            (t.pub PI_TABLE) (t.pub PI_INITIAL) (t.pub PI_FINAL) (t.pub PI_ROUTE) gRows)
    (hlen : t.rows.length = gRows.length) :
    t.pub PI_FINAL = classify (pinnedDfa (t.pub PI_INITIAL)) (symbols (traceRows t)) := by
  letI := dfaPrims hash
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hne_tr : traceRows t ≠ [] := by
    simp only [traceRows, ne_eq, List.map_eq_nil_iff]; exact hne
  -- (a) t's running chain folds tableCommitment over its entry hashes, pinned to routeCommitment by B3
  have hseed_t : ∀ r₀, (traceRows t).head? = some r₀ →
      r₀.running = CryptoPrimitives.compress (t.pub PI_TABLE) r₀.entryHash := by
    intro r₀ hr₀
    simp only [traceRows, List.head?_map, Option.map_eq_some_iff] at hr₀
    obtain ⟨a, hah, rfl⟩ := hr₀
    have h0 : t.rows[0]'hpos = a := by
      rw [List.head?_eq_some_head hne] at hah
      have hh : t.rows.head hne = a := Option.some.inj hah
      rw [← hh, List.head_eq_getElem hne]
    show (mkRow a).running = hash [t.pub PI_TABLE, (mkRow a).entryHash]
    have hr := running_eq hsat hchip hwire hpos
    have hacc := piFirst_forces hsat hne mem_seedAccPin
    rw [envAt_loc hpos, h0] at hacc
    -- the seed pin binds only mod p; the ACC cell + the table PI are canonical, so it lifts to ℤ.
    have haccZ : a ACC = t.pub PI_TABLE := by
      have hca := (hchain.1 0 hpos).1
      rw [h0] at hca
      exact eq_of_modEq_of_canon hacc hca.1 hca.2 hchain.2.1.1 hchain.2.1.2
    rw [h0, haccZ] at hr
    simpa only [mkRow] using hr
  have haccum_t : @Accumulates ℤ ℤ ℤ _ (dfaPrims hash) (traceRows t) := by
    apply accumulates_map hash t.rows (fun i hi => running_eq hsat hchip hwire hi)
    intro i hi
    have hi0 : i < t.rows.length := Nat.lt_of_succ_lt hi
    have hw := window_forces hsat hi0 (Nat.ne_of_lt hi) mem_copyForwardWindow rfl
    -- the copy-forward window binds only mod p; both spine cells are canonical, so it lifts to ℤ.
    have hcm : (envAt t i).nxt ACC ≡ (envAt t i).loc RUNNING_HASH [ZMOD 2013265921] :=
      (gate_modEq_iff (by simp only [copyForwardBody_eq, WindowExpr.eval]; ring)).mp hw
    rw [envAt_nxt hi, envAt_loc hi0] at hcm
    exact eq_of_modEq_of_canon hcm ((hchain.1 (i + 1) hi).1).1 ((hchain.1 (i + 1) hi).1).2
      ((hchain.1 i hi0).2).1 ((hchain.1 i hi0).2).2
  have hlast_tr : (traceRows t).getLast? = some (mkRow (t.rows.getLast hne)) := by
    rw [traceRows, List.getLast?_map, List.getLast?_eq_some_getLast hne]; rfl
  have hrun_last := lastRunning_eq_fold (t.pub PI_TABLE) (traceRows t) hne_tr hseed_t haccum_t
    (mkRow (t.rows.getLast hne)) hlast_tr
  have hb3 := piLast_forces hsat hne mem_b3RoutePin
  rw [envAt_loc hlt] at hb3
  -- the B3 route pin binds only mod p; the last RUNNING_HASH cell + the route PI are canonical.
  have hb3Z : (t.rows[t.rows.length - 1]'hlt) RUNNING_HASH = t.pub PI_ROUTE :=
    eq_of_modEq_of_canon hb3 ((hchain.1 _ hlt).2).1 ((hchain.1 _ hlt).2).2
      hchain.2.2.1 hchain.2.2.2
  have hfold_t : t.pub PI_ROUTE = runningFold (t.pub PI_TABLE) (entryHashes (traceRows t)) := by
    have h1 : (mkRow (t.rows.getLast hne)).running = t.pub PI_ROUTE := by
      show (t.rows.getLast hne) RUNNING_HASH = t.pub PI_ROUTE
      rw [List.getLast_eq_getElem hne]; exact hb3Z
    rw [← h1]; exact hrun_last
  -- (b) g's running chain folds the SAME tableCommitment to the SAME routeCommitment
  have hfold_g : t.pub PI_ROUTE = runningFold (t.pub PI_TABLE) (entryHashes gRows) := by
    have hlg : gRows.getLast? = some (gRows.getLast hg.nonempty) :=
      List.getLast?_eq_some_getLast hg.nonempty
    have hrun_g := lastRunning_eq_fold (t.pub PI_TABLE) gRows hg.nonempty hg.seed hg.accum
      (gRows.getLast hg.nonempty) hlg
    rw [← hg.routeBoundary _ hlg]; exact hrun_g
  -- (c) the binding: equal folds ⇒ equal entry-hash chains (fold_inj / CR)
  have hlen' : (entryHashes (traceRows t)).length = (entryHashes gRows).length := by
    simp only [entryHashes, traceRows, List.length_map]; exact hlen
  have hEH : entryHashes (traceRows t) = entryHashes gRows :=
    fold_inj cf (entryHashes (traceRows t)) (entryHashes gRows) hlen' (t.pub PI_TABLE) (by
      rw [← hfold_t, ← hfold_g])
  -- (d) last entry hashes agree ⇒ (compressN-CR) last triples agree ⇒ hterm
  have hlast_EH : (t.rows.getLast hne) ENTRY_HASH = (gRows.getLast hg.nonempty).entryHash := by
    have hc := congrArg List.getLast? hEH
    simp only [entryHashes, traceRows, List.getLast?_map, List.getLast?_eq_some_getLast hne,
      List.getLast?_eq_some_getLast hg.nonempty, Option.map_some, Option.some.injEq] at hc
    simpa only [mkRow] using hc
  set alast := t.rows.getLast hne with halast
  set glast := gRows.getLast hg.nonempty with hglast
  have hgmem : glast ∈ gRows := List.getLast_mem hg.nonempty
  have hentry_a : alast ENTRY_HASH
      = hash [alast CURRENT, alast SYMBOL, alast NEXT, alast ZERO_LANE] := by
    have := entry_eq hsat hchip hwire hlt
    rw [← List.getLast_eq_getElem hne] at this; exact this
  have hentry_g : glast.entryHash = hash [glast.state, glast.sym, glast.next, 0] := by
    have := hg.entry glast hgmem
    simp only [entryHashOf, id_eq, dfaPrims] at this
    exact this
  have hcompressN : hash [alast CURRENT, alast SYMBOL, alast NEXT, alast ZERO_LANE]
      = hash [glast.state, glast.sym, glast.next, 0] := by
    rw [← hentry_a, ← hentry_g]; exact hlast_EH
  have htriple := cf.compressN_inj _ _ hcompressN
  have hnext : alast NEXT = glast.next := by
    have h2 := (List.cons.injEq _ _ _ _).mp htriple |>.2
    have h3 := (List.cons.injEq _ _ _ _).mp h2 |>.2
    exact ((List.cons.injEq _ _ _ _).mp h3).1
  have hcur : alast CURRENT = glast.state := ((List.cons.injEq _ _ _ _).mp htriple).1
  have hsym : alast SYMBOL = glast.sym :=
    ((List.cons.injEq _ _ _ _).mp ((List.cons.injEq _ _ _ _).mp htriple).2).1
  have hgtable : glast.next = toggleStep glast.state glast.sym := hg.table glast hgmem
  have hterm : transitionBody.eval (t.rows.getD (t.rows.length - 1) zeroAsg) = 0 := by
    rw [getD_row hlt, ← List.getLast_eq_getElem hne]
    refine (transition_body_zero_iff alast).mpr ?_
    show alast NEXT = alast CURRENT + alast SYMBOL - 2 * (alast CURRENT * alast SYMBOL)
    rw [hnext, hgtable, hcur, hsym]; rfl
  exact (dfaRouting_refines_classify hsat hne hcanon hterm).2.2

#assert_axioms dfaRouting_rung2
#assert_axioms collisionFree_of_injective

/-! ## §6 — Non-vacuity, FALSE half: `Satisfied2` alone does NOT force `final = classify`.

The honest genuine 2-row toggle run `IDLE=0 →1 1 →1 0` (reading `[1,1]`, `classify = 0`) with its LAST
edge FLIPPED to the forbidden `1 →1 1`: the transition gate is divided by the transition zerofier so
it is vacuous on the last row, both chip lookups still hold (membership), and B2/B3 pin the fake
`final = 1`. The trace PROVABLY `Satisfied2`s, yet `final = 1 ≠ 0 = classify [1,1]`. So the RUNG-2
route-commitment anchor (a genuine reference run matching the disclosed commitment) is LOAD-BEARING —
the conclusion is impossible from `Satisfied2` alone. -/

/-- The flipped LAST row: `current=1, symbol=1, next=1` (the forbidden edge `step(1,1)=0` claimed as
`1`). -/
def cheatRow1 : Assignment := rowOf [1, 1, 1, 0, 0, 0, 0, 0]

/-- Public inputs pinning the FAKE final state `1` (and `route/table/initial` to `0`). -/
def cheatPub : Assignment := rowOf [0, 1, 0, 0]

/-- The chip table carrying the two rows' entry/running tuples (so both lookups hold on both rows). -/
def cheatChipTbl : List (List ℤ) :=
  [entryTupleAt wr0, runTupleAt wr0, entryTupleAt cheatRow1, runTupleAt cheatRow1]

def cheatTf : TraceFamily := fun id =>
  match id with
  | .poseidon2 => cheatChipTbl
  | .custom 3  => narrowTable cheatChipTbl
  | _ => []

/-- The cheating 2-row trace: genuine row 0, flipped last row. -/
def cheatTrace : VmTrace := { rows := [wr0, cheatRow1], pub := cheatPub, tf := cheatTf }

/-- **The cheat PROVABLY `Satisfied2`s** — the flipped last edge escapes the transition gate (vacuous
on the last row), the lookups hold by membership, and the boundary pins accept the fake final. -/
theorem cheatTrace_satisfied2 :
    Satisfied2 hash0 dfaRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] cheatTrace where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    clear hi
    rw [show cheatTrace.rows.length = 2 from rfl]
    simp only [dfaRoutingDesc] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        WindowConstraint.holdsAt, entryHashLookup, runningHashLookup, zeroLaneGate, isFirstBoolGate_eq,
        stateGridGate_eq, symbolGridGate_eq, transitionGate, continuityWindow, copyForwardWindow,
        b1InitialPin, isFirstPinned, seedAccPin, b2FinalPin, b3RoutePin, cheatTrace, cheatTf,
        cheatPub, Nat.reduceAdd, Nat.reduceBEq, reduceIte, reduceCtorEq] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [dfaRoutingDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_dfa]; simp
  memDisciplined := by rw [memLog_dfa]; trivial
  memBalanced := by rw [memLog_dfa]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_dfa]; rfl
  mapTableFaithful := by rw [mapLog_dfa]; rfl

/-- **The cheat's exposed `final ≠ classify(input)`.** `final = 1` (the flipped last edge), but the
genuine classification of the read input `[1,1]` is `0` — the toggle `0 →1 1 →1 0`. So no
`Satisfied2`-only theorem could conclude `final = classify`. -/
theorem cheat_final_ne_classify :
    cheatTrace.pub PI_FINAL
      ≠ classify (pinnedDfa (cheatTrace.pub PI_INITIAL)) (symbols (traceRows cheatTrace)) := by
  rw [symbols_traceRows]
  decide

/-! ## §7 — Non-vacuity, TRUE half: the RUNG-2 discharge FIRES on a genuine witness.

A genuine 1-row toggle run `IDLE=0 →symbol=1 1` (reading `[1]`, `classify = 1`) over a REAL injective
`hash` (so the CR carrier is discharged from `Function.Injective hash` via `collisionFree_of_injective`
— the same shape `DfaAcceptanceAir.Reference` uses). Every hypothesis of `dfaRouting_rung2` is met — the
descriptor `Satisfied2`, a SOUND chip table, the CR carrier, and the honest genuine reference run `g`
(itself) with the matching public route commitment — and the discharged conclusion FIRES:
`final = 1 = classify (pinnedDfa 0) [1]`. So the hypothesis set is jointly satisfiable and the RUNG-2
conclusion is achievably true (not vacuous). -/

section TrueWitness
variable (hash : List ℤ → ℤ)

/-- The 1-row genuine trace's row: `current=0, symbol=1, next=1` (`step(0,1)=1`), with the two Poseidon2
columns carrying the genuine `entry = hash[0,1,1,0]`, `running = hash[0, entry]` (seed
`table_commitment = 0`), `is_first=1`, `acc=0`. -/
def wtRow0 : Assignment := rowOf [0, 1, 1, hash [0, 1, 1, 0], hash [0, hash [0, 1, 1, 0]], 1, 0, 0]

/-- Public inputs: `initial=0`, `final=1` (the genuine classification), `table=0` (seed),
`route = running` (the honest route commitment). -/
def wtPub : Assignment := rowOf [0, 1, 0, hash [0, hash [0, 1, 1, 0]]]

/-- The sound chip table carrying exactly the row's entry / running tuples. -/
def wtChipTbl : List (List ℤ) := [entryTupleAt (wtRow0 hash), runTupleAt (wtRow0 hash)]

def wtTf : TraceFamily := fun id =>
  match id with
  | .poseidon2 => wtChipTbl hash
  | .custom 3  => narrowTable (wtChipTbl hash)
  | _ => []

/-- The 1-row genuine trace. -/
def wtTrace : VmTrace := { rows := [wtRow0 hash], pub := wtPub hash, tf := wtTf hash }

/-- **The chip table is SOUND** — each row IS a genuine `chipRow` of the permutation (`hash`). -/
theorem wtTf_chipSound : ChipTableSound hash ((wtTrace hash).tf .poseidon2) := by
  intro r hr
  simp only [wtTrace, wtTf, wtChipTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[0, 1, 1, 0], List.replicate 7 0, by decide, by decide, rfl⟩
  · exact ⟨[0, hash [0, 1, 1, 0]], List.replicate 7 0,
      by simp only [List.length_cons, List.length_nil]; decide, by decide, rfl⟩

/-- **The genuine witness wires the NARROW bus to the 18-prefix of its wide chip table** —
definitional, exactly the deployed Rust `narrow_hist` serving (one physical chip, two buses). -/
theorem wtTf_narrow_wire :
    (wtTrace hash).tf poseidon2narrow = narrowTable ((wtTrace hash).tf .poseidon2) := rfl

/-- **The 1-row trace `Satisfied2`s the descriptor** — the two lookups by membership in the sound chip
table, the per-row gates vacuous on the single (= last) row, and the boundary pins met. -/
theorem wtTrace_satisfied2 :
    Satisfied2 hash dfaRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] (wtTrace hash) where
  rowConstraints := by
    intro i hi c hc
    have hi1 : i < 1 := hi
    interval_cases i
    simp only [dfaRoutingDesc] at hc
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        WindowConstraint.holdsAt, entryHashLookup, runningHashLookup, zeroLaneGate, isFirstBoolGate_eq,
        stateGridGate_eq, symbolGridGate_eq, transitionGate, continuityWindow, copyForwardWindow,
        b1InitialPin, isFirstPinned, seedAccPin, b2FinalPin, b3RoutePin, wtTrace, wtTf, envAt,
        zeroAsg, List.getD_cons_zero, List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceBEq, reduceIte, reduceCtorEq] <;>
      first
        | exact List.mem_cons.mpr (Or.inl rfl)
        | exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        | trivial
        | simp [wtRow0, wtPub, rowOf, EmittedExpr.eval, CURRENT, SYMBOL, NEXT, IS_FIRST,
            ZERO_LANE, ACC, RUNNING_HASH, PI_INITIAL, PI_FINAL, PI_TABLE, PI_ROUTE]
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [dfaRoutingDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_dfa]; simp
  memDisciplined := by rw [memLog_dfa]; trivial
  memBalanced := by rw [memLog_dfa]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_dfa]; rfl
  mapTableFaithful := by rw [mapLog_dfa]; rfl

/-- The GENUINE reference run (the honest anchor): the same 1-row toggle run, as a `Row` list, with
`entryHash`/`running` the real Poseidon2 chain. Since the witness IS genuine, `g` is the trace itself. -/
def wtG : List (Row ℤ ℤ ℤ) :=
  [{ state := 0, sym := 1, next := 1, entryHash := hash [0, 1, 1, 0],
     running := hash [0, hash [0, 1, 1, 0]] }]

/-- **`g` satisfies the full `DfaAcceptanceAir.Satisfies`** (over the pinned toggle DFA, `id`
encodings, seed `0`, publics `(0, 1, running)`) — every conjunct holds for the genuine run. -/
theorem wtG_satisfies :
    @Satisfies ℤ ℤ ℤ _ (dfaPrims hash) (pinnedDfa 0) id id 0 0 1 (hash [0, hash [0, 1, 1, 0]])
      (wtG hash) :=
  letI := dfaPrims hash
  { nonempty := by simp [wtG]
    entry := by intro r hr; simp only [wtG, List.mem_singleton] at hr; subst hr; rfl
    table := by intro r hr; simp only [wtG, List.mem_singleton] at hr; subst hr; rfl
    cont := by simp only [wtG]; trivial
    seed := by intro r₀ hr₀; simp only [wtG, List.head?_cons, Option.some.injEq] at hr₀; subst hr₀; rfl
    accum := by simp only [wtG]; trivial
    initBoundary := by
      intro r₀ hr₀; simp only [wtG, List.head?_cons, Option.some.injEq] at hr₀; subst hr₀; rfl
    finalBoundary := by
      intro rₙ hlast; simp only [wtG, List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast; rfl
    routeBoundary := by
      intro rₙ hlast; simp only [wtG, List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast; rfl }

/-- **The witness inhabits the DFA canonicality envelope** — its DFA cells are `0`/`1` and both
bound public inputs are `0`/`1`, all canonical representatives. -/
theorem wtTrace_dfaCanon : DfaTraceCanon (wtTrace hash) := by
  refine ⟨fun i hi => ?_,
    ⟨show (0:ℤ) ≤ 0 by decide, show (0:ℤ) < 2013265921 by decide⟩,
    ⟨show (0:ℤ) ≤ 1 by decide, show (1:ℤ) < 2013265921 by decide⟩⟩
  have hi1 : i < 1 := hi
  interval_cases i
  exact ⟨⟨show (0:ℤ) ≤ 0 by decide, show (0:ℤ) < 2013265921 by decide⟩,
         ⟨show (0:ℤ) ≤ 1 by decide, show (1:ℤ) < 2013265921 by decide⟩,
         ⟨show (0:ℤ) ≤ 1 by decide, show (1:ℤ) < 2013265921 by decide⟩⟩

/-- **The witness inhabits the chain canonicality envelope**, given that the (single) route digest
`hash [0, hash [0,1,1,0]]` is a canonical field value — the honest situation for a genuine
field-valued Poseidon2. The seed cells (`ACC = 0`, `pi[table] = 0`) are canonical outright. -/
theorem wtTrace_chainCanon
    (hcanR : 0 ≤ hash [0, hash [0, 1, 1, 0]] ∧ hash [0, hash [0, 1, 1, 0]] < 2013265921) :
    DfaChainCanon (wtTrace hash) := by
  refine ⟨fun i hi => ?_,
    ⟨show (0:ℤ) ≤ 0 by decide, show (0:ℤ) < 2013265921 by decide⟩,
    ⟨hcanR.1, hcanR.2⟩⟩
  have hi1 : i < 1 := hi
  interval_cases i
  exact ⟨⟨show (0:ℤ) ≤ 0 by decide, show (0:ℤ) < 2013265921 by decide⟩,
         ⟨hcanR.1, hcanR.2⟩⟩

/-- The explicit trace has the correct classification for every hash. Its endpoint
and input do not depend on injectivity or canonicality, so those assumptions are
unnecessary here. `refWitness_fires` below separately invokes the full Rung-2
soundness theorem with its jointly proved reference premises. -/
theorem wtTrace_rung2_fires :
    (wtTrace hash).pub PI_FINAL
      = classify (pinnedDfa ((wtTrace hash).pub PI_INITIAL)) (symbols (traceRows (wtTrace hash))) := by
  have hs : symbols (traceRows (wtTrace hash)) = [1] := by rw [symbols_traceRows]; rfl
  rw [hs]
  rfl

/-- The recovered value is the genuine toggle endpoint `1` over the read input `[1]`
(`classify (pinnedDfa 0) [1] = 1`) — the conclusion is a real classification, not a constant. -/
theorem wtTrace_value :
    (wtTrace hash).pub PI_FINAL = 1
    ∧ classify (pinnedDfa ((wtTrace hash).pub PI_INITIAL)) (symbols (traceRows (wtTrace hash))) = 1 := by
  refine ⟨rfl, ?_⟩
  have hs : symbols (traceRows (wtTrace hash)) = [1] := by rw [symbols_traceRows]; rfl
  rw [hs]; rfl

end TrueWitness

/-! ## §7b — the reference hash: the RUNG-2 hypothesis set is JOINTLY satisfiable.

`Function.Injective hash` (the CR reference realization) and canonicality of the witness's route
digest are exhibited TOGETHER on one concrete hash: the two witness digests are pinned to the
reserved canonical values `1` / `2`, and every other list rides the injective `Encodable.encode`
shifted past them — injective as a whole, canonical where the witness reads it. So neither envelope
hypothesis of the actual Rung-2 application in `refWitness_fires` is vacuous, jointly or alone. -/

/-- The reference hash: `[0,1,1,0] ↦ 1`, `[0,1] ↦ 2`, everything else `encode + 3`. -/
def refHash : List ℤ → ℤ := fun l =>
  if l = [0, 1, 1, 0] then 1
  else if l = [0, 1] then 2
  else (Encodable.encode l : ℤ) + 3

/-- The reference hash is injective (the reserved values `1`/`2` sit below the shifted encodings,
which are themselves injective). -/
theorem refHash_injective : Function.Injective refHash := by
  intro a b h
  simp only [refHash] at h
  split_ifs at h
  all_goals subst_vars
  all_goals try rfl
  all_goals try omega
  exact Encodable.encode_injective (by omega)

/-- The witness's route digest is canonical over the reference hash (`refHash [0, refHash [0,1,1,0]]
= refHash [0,1] = 2`). -/
theorem refHash_route_canon :
    0 ≤ refHash [0, refHash [0, 1, 1, 0]] ∧ refHash [0, refHash [0, 1, 1, 0]] < 2013265921 := by
  have h1 : refHash [0, 1, 1, 0] = 1 := by simp [refHash]
  rw [h1]
  have h2 : refHash [0, 1] = 2 := by simp [refHash]
  rw [h2]
  norm_num

/-- **The joint hypothesis set is INHABITED**: over the reference hash the RUNG-2 discharge fires
end-to-end with concrete values. -/
theorem refWitness_fires :
    (wtTrace refHash).pub PI_FINAL
      = classify (pinnedDfa ((wtTrace refHash).pub PI_INITIAL))
          (symbols (traceRows (wtTrace refHash))) :=
  dfaRouting_rung2 (wtTrace_satisfied2 refHash) (by simp [wtTrace]) (wtTrace_dfaCanon refHash)
    (wtTrace_chainCanon refHash refHash_route_canon) (wtTf_chipSound refHash)
    (wtTf_narrow_wire refHash) (collisionFree_of_injective refHash_injective)
    (wtG refHash) (wtG_satisfies refHash) rfl

/-! ## §8 — Axiom tripwires. -/

#assert_axioms cheatTrace_satisfied2
#assert_axioms cheat_final_ne_classify
#assert_axioms wtTf_chipSound
#assert_axioms wtTf_narrow_wire
#assert_axioms wtTrace_satisfied2
#assert_axioms wtG_satisfies
#assert_axioms wtTrace_rung2_fires
#assert_axioms wtTrace_value
#assert_axioms refHash_injective
#assert_axioms refWitness_fires

/-- info: 'Dregg2.Circuit.Emit.DfaRoutingRung2.collisionFree_of_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms collisionFree_of_injective
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingRung2.wtTrace_rung2_fires' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wtTrace_rung2_fires
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingRung2.refWitness_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refWitness_fires

end Dregg2.Circuit.Emit.DfaRoutingRung2
