/-
# Dregg2.Circuit.Emit.DfaRoutingChainBound — the content-bound statement for the hash-chained
DFA-routing family (L2).

Lane E, `docs/automata/SUBSTRATE-DECISION.md` §5.2 ("no family's theorem reads the word off a
private trace"); `docs/automata/AUTOMATA-ARITHMETIZATION-PROGRAM.md` §1.2 names this corollary as
the cheap follow-up. 2026-11-06.

## The family

The routing AIR modeled in `Dregg2/Crypto/DfaAcceptanceAir.lean` and served as the emitted toggle
descriptor `dfaRoutingDesc` (`DfaRoutingEmit.lean`): rows `(current, symbol, next, entry_hash,
running_hash, …)`, `entry_hash = H(current, symbol, next, zero_lane)` and `running = H(acc, entry)`
by chip lookups on EVERY row, `acc` seeded at `pi[table]` and carried forward, the last `running`
pinned to `pi[route]`. The public `route_commitment` is a commitment to the whole run, hence to the
word, but no theorem said so: `dfaAir_verify_sound` concludes `finalState = classify d (symbols
rows)` with `symbols rows` read off the private trace, and `DfaRoutingRung2.dfaRouting_rung2` needs a
whole genuine reference run `g` as its anchor.

## What is proved

Model level (`DfaAcceptanceAir`, abstract `CryptoPrimitives`):
  * `wordCommit d encState encSym tc q₀ w` — the route commitment OF A WORD: the running fold, seeded
    at `tc`, of the entry hashes of `w`'s deterministic run from `q₀`. A function of the record.
  * `route_eq_wordCommit` (the hub's explicit corollary): `Satisfies … rows →
    routeCommitment = wordCommit … (symbols rows)`.
  * `dfaAir_bound_verify_sound` (the `Dfa.BoundStatement` shape): an accepted proof yields `∃ w,
    wordCommit … w = routeCommitment ∧ finalState = classify d w ∧ ∃ rows, Satisfies … rows ∧
    symbols rows = w`.
  * `wordCommit_injective`: under `CollisionFree` and an injective symbol encoding, two words of
    the same length with the same commitment are equal; hence
    `dfaAir_bound_identifies_record`: an accepted proof and a record whose commitment is the public
    one yield a satisfying trace that READS the record, classified to `finalState`, or a trace of a
    different length. Only the given statement's `encSym` is required injective;
    `identifies_record_inhabited` meets every hypothesis over `Sy = ℤ` (a reference kernel
    `refKernel` that decides `Satisfies`). Both are IDEAL INJECTIVE-HASH lemmas (residual 1).

Deployed form, over the descriptor's own `hash : List ℤ → ℤ`, no injectivity floor (§1½):
  * `chain_binds_or_collides` — two equal-length preimage lists with one seeded chain are equal, or
    the deterministic extractor `chainFind` returns a `SpongeColl hash` pair ON THOSE TWO CHAINS (the
    latest fold step whose inputs differ, else the first differing entry preimage);
    `chainFind_self`: one list never triggers it. The `Lightclient.MMR.mroot_binds_or_collides`
    shape.

Descriptor level (the served `dfaRoutingDesc`, `Satisfied2` over its own `hash`):
  * `route_eq_fold` — `pi[route] = runningFold pi[table] (entry-hash column)`, from the chip
    lookups, the copy-forward window and the seed / B3 pins (the first half of `dfaRouting_rung2`,
    stated on its own).
  * ⚑ `dfaRouting_bound` — THE CONTENT-BOUND THEOREM: for a record `w` with `pi[route] =
    wordCommit hash pi[table] pi[initial] w` and `|w| = |rows|`, a satisfying trace (sound chip
    table, CR carrier, the two canonicality envelopes) READS `w` (`symbols = w`) and `pi[final] =
    classify w`. No genuine reference run, no `hterm`: the commitment computed from the record is
    the anchor. Every row's `(current, symbol, next, zero_lane)` is pinned by the chain alone.
  * `dfaRouting_bound_accepts` — the whole-run corollary: if `pi[final]` is accepting, the record's
    run from `pi[initial]` is an accepting run (`accepts (classify w)`).
  * ⚑ `dfaRouting_bound_or_collides` — the same conclusion with NO `CollisionFree`: bound, or
    `SpongeColl hash (boundFind hash t w)` at the trace's and the record's chains.
    `dfaRouting_bound` is its ideal-hash corollary.
  * `BoundAccepts` (satisfied, record opens `pi[route]`, record of the trace's length) and
    `boundAccepts_sound`; `UnboundAccepts` is the record-ignoring acceptance.

## Falsifier (§4, kernel-checked)

On the genuine 1-row witness `DfaRoutingRung2.wtTrace refHash` (reads `[1]`, `final = 1`):
`splice_separation` — for the one trace and the one record `[0]`, `UnboundAccepts` holds,
`BoundAccepts` fails (the record-opening equality fails, `splice_route_mismatch`), and the claim
`final = classify [0]` is false. `wt_boundAccepts`: the honest record `[1]` is bound-accepted;
`wt_bound_or_collides` / `wt_no_collision`: the deployed form fires, and its collision branch is
false for the honest trace by `chainFind_self` alone (no property of the hash is used).

## NOT claimed / residuals
  * (1) `wordCommit_injective`, `dfaAir_bound_identifies_record` and `dfaRouting_bound` assume
    `CollisionFree` (`compressN_inj`, global injectivity of the sponge, impossible for a finite
    digest carrier): IDEAL INJECTIVE-HASH LEMMAS, NOT DEPLOYED COLLISION-RESISTANCE REDUCTIONS. The
    deployed statement is `dfaRouting_bound_or_collides`; the model level (abstract `Digest`) has
    no extractor form here.
  * The length of the record is a hypothesis (`|w| = |rows|`): the running fold is injective only
    across equal lengths (`fold_inj`), and the statement does not carry the trace length. A STARK's
    trace length is public; binding it into the statement is a one-field change, not made here.
  * `ChipTableSound` rides as a named hypothesis (as in Rung 2); the reference `refHash` inhabits
    it and `CollisionFree`. The canonicality envelopes `DfaTraceCanon`, `DfaChainCanon` are Rung 1/2's.
  * The zero lane of the LAST row is not pinned by a gate (gates are divided by the transition
    zerofier); `dfaRouting_bound` gets it from the chain (`compressN` injectivity), so it is not a
    hole for the bound statement (`rows_of_pre` reads it off the preimage equality), but
    `route_eq_wordCommit` at the descriptor level needs it.
  * No new column, no new descriptor; this is a statement over the served one.

Codex round 4 (2026-11-06) items 1, 3 and 5 are repaired here.

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}. Imports read-only.
-/
import Dregg2.Circuit.Emit.DfaRoutingRung2
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.Emit.DfaRoutingChainBound

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.DfaRoutingEmit
open Dregg2.Circuit.Emit.DfaRoutingRefine
open Dregg2.Circuit.Emit.DfaRoutingRung2
open Dregg2.Circuit.ChipNarrowLookup (narrowTable)
open Dregg2.Crypto (CryptoPrimitives)
open Dregg2.Crypto.DfaAcceptanceAir
  (TableDfa Row classify classifyFrom symbols Satisfies Continuous Accumulates CollisionFree
   runningFold entryHashes entryHashOf lastRunning_eq_fold fold_inj DfaAirVerifierKernel
   classifyFrom_cons classifyFrom_nil)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Circuit.Poseidon2Binding (SpongeColl)

set_option autoImplicit false

/-! ## §1 — The commitment of a word (model level). -/

section Model

variable {State Sym Digest : Type} [AddCommGroup Digest] [CryptoPrimitives Digest]

/-- The entry hashes of the deterministic run of `w` from `q`. -/
def runEntries (d : TableDfa State Sym) (encState : State → Digest) (encSym : Sym → Digest) :
    State → List Sym → List Digest
  | _, [] => []
  | q, y :: ys => entryHashOf encState encSym q y (d.step q y) :: runEntries d encState encSym (d.step q y) ys

theorem runEntries_length (d : TableDfa State Sym) (encState : State → Digest)
    (encSym : Sym → Digest) : ∀ (q : State) (w : List Sym),
    (runEntries d encState encSym q w).length = w.length
  | _, [] => rfl
  | q, _ :: ys => by simp [runEntries, runEntries_length d encState encSym _ ys]

/-- ⚑ **`wordCommit`** — the route commitment of a WORD: the running fold, seeded at `tc`, of the
entry hashes of its run from `q₀`. Computable by anyone holding the record and the public table. -/
def wordCommit (d : TableDfa State Sym) (encState : State → Digest) (encSym : Sym → Digest)
    (tc : Digest) (q₀ : State) (w : List Sym) : Digest :=
  runningFold tc (runEntries d encState encSym q₀ w)

/-- A genuine run's entry-hash column is the run entries of its word. -/
theorem entryHashes_eq_runEntries (d : TableDfa State Sym) (encState : State → Digest)
    (encSym : Sym → Digest) : ∀ (rows : List (Row State Sym Digest)) (q : State),
    (∀ r ∈ rows, r.entryHash = entryHashOf encState encSym r.state r.sym r.next) →
    (∀ r ∈ rows, r.next = d.step r.state r.sym) →
    Continuous rows →
    (∀ r₀, rows.head? = some r₀ → r₀.state = q) →
    entryHashes rows = runEntries d encState encSym q (symbols rows)
  | [], _, _, _, _, _ => rfl
  | a :: rest, q, hentry, htable, hcont, hhead => by
    have ha : a.state = q := hhead a rfl
    have hn : a.next = d.step a.state a.sym := htable a List.mem_cons_self
    have hrest : entryHashes rest = runEntries d encState encSym (d.step q a.sym) (symbols rest) := by
      refine entryHashes_eq_runEntries d encState encSym rest _
        (fun r hr => hentry r (List.mem_cons_of_mem _ hr))
        (fun r hr => htable r (List.mem_cons_of_mem _ hr)) ?_ ?_
      · cases rest with
        | nil => trivial
        | cons b bs => exact hcont.2
      · intro r₀ hr₀
        cases rest with
        | nil => simp at hr₀
        | cons b bs =>
          simp only [List.head?_cons, Option.some.injEq] at hr₀
          subst hr₀
          rw [hcont.1, hn, ha]
    show a.entryHash :: entryHashes rest = runEntries d encState encSym q (a.sym :: symbols rest)
    rw [hentry a List.mem_cons_self, hrest, hn, ha]
    rfl

theorem exists_getLast' {α : Type} : ∀ (l : List α), l ≠ [] → ∃ x, l.getLast? = some x
  | [], h => absurd rfl h
  | a :: as, _ => ⟨(a :: as).getLast (by simp), by simp [List.getLast?_eq_some_getLast]⟩

/-- ⚑ **`route_eq_wordCommit`** — the hub's explicit corollary: the public route commitment of a
satisfying trace is the commitment of the word the trace reads. -/
theorem route_eq_wordCommit (d : TableDfa State Sym) (encState : State → Digest)
    (encSym : Sym → Digest) (tc : Digest) (q₀ fin : State) (route : Digest)
    (rows : List (Row State Sym Digest))
    (h : Satisfies d encState encSym tc q₀ fin route rows) :
    route = wordCommit d encState encSym tc q₀ (symbols rows) := by
  obtain ⟨rₙ, hl⟩ := exists_getLast' rows h.nonempty
  rw [← h.routeBoundary rₙ hl, lastRunning_eq_fold tc rows h.nonempty h.seed h.accum rₙ hl,
    wordCommit, entryHashes_eq_runEntries d encState encSym rows q₀ h.entry h.table h.cont
      h.initBoundary]

/-- Equal run entries from one state force equal words, under CR and an injective symbol code. -/
theorem runEntries_inj (cf : CollisionFree Digest) (d : TableDfa State Sym)
    (encState : State → Digest) (encSym : Sym → Digest) (hsym : Function.Injective encSym) :
    ∀ (q : State) (w₁ w₂ : List Sym),
    runEntries d encState encSym q w₁ = runEntries d encState encSym q w₂ → w₁ = w₂
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by simp [runEntries] at h
  | _, _ :: _, [], h => by simp [runEntries] at h
  | q, y₁ :: ys₁, y₂ :: ys₂, h => by
    simp only [runEntries, List.cons.injEq] at h
    obtain ⟨hh, ht⟩ := h
    have hl := cf.compressN_inj _ _ hh
    simp only [List.cons.injEq] at hl
    have hy : y₁ = y₂ := hsym hl.2.1
    subst hy
    rw [runEntries_inj cf d encState encSym hsym _ ys₁ ys₂ ht]

/-- ⚑ **`wordCommit_injective`** — two words of one length with one commitment are equal, under
`CollisionFree` and an injective symbol encoding. An IDEAL INJECTIVE-HASH LEMMA, not a deployed
collision-resistance reduction: `CollisionFree.compressN_inj` is global injectivity of the sponge,
impossible for a finite digest carrier. The deployed form is `chain_binds_or_collides` (§2). -/
theorem wordCommit_injective (cf : CollisionFree Digest) (d : TableDfa State Sym)
    (encState : State → Digest) (encSym : Sym → Digest) (hsym : Function.Injective encSym)
    (tc : Digest) (q₀ : State) {w₁ w₂ : List Sym} (hlen : w₁.length = w₂.length)
    (h : wordCommit d encState encSym tc q₀ w₁ = wordCommit d encState encSym tc q₀ w₂) :
    w₁ = w₂ :=
  runEntries_inj cf d encState encSym hsym q₀ w₁ w₂
    (fold_inj cf _ _ (by simp [runEntries_length, hlen]) tc h)

variable {St Sy Dg : Type} [AddCommGroup Dg] [CryptoPrimitives Dg] {Proof : Type}

/-- ⚑ **`dfaAir_bound_verify_sound`** — the `Dfa.BoundStatement` shape for the routing AIR: an
accepted proof yields a word committing to the public `routeCommitment`, classified to the public
`finalState`, read by a satisfying trace. -/
theorem dfaAir_bound_verify_sound [K : DfaAirVerifierKernel St Sy Dg Proof]
    (hext : K.extractable) (stmt : Dregg2.Crypto.DfaAcceptanceAir.Statement St Sy Dg)
    (proof : Proof) (hstart : stmt.d.start = stmt.initialState)
    (haccept : K.verify stmt proof = true) :
    ∃ w : List Sy,
      wordCommit stmt.d stmt.encState stmt.encSym stmt.tableCommitment stmt.initialState w
        = stmt.routeCommitment ∧
      stmt.finalState = classify stmt.d w ∧
      ∃ rows, Satisfies stmt.d stmt.encState stmt.encSym stmt.tableCommitment stmt.initialState
        stmt.finalState stmt.routeCommitment rows ∧ symbols rows = w := by
  obtain ⟨rows, hsat, hfin⟩ :=
    Dregg2.Crypto.DfaAcceptanceAir.dfaAir_verify_sound hext stmt proof hstart haccept
  exact ⟨symbols rows, (route_eq_wordCommit _ _ _ _ _ _ _ rows hsat).symm, hfin, rows, hsat, rfl⟩

/-- ⚑ **`dfaAir_bound_identifies_record`** — the record form: for a record whose commitment is the
public one, an accepted proof yields a satisfying trace that READS THE RECORD and classifies it to
`finalState`, or a trace of a different length (the alternative the model statement leaves open:
it carries no trace length). An ideal injective-hash lemma (see `wordCommit_injective`). Only THIS
statement's symbol encoding is required injective; `identifies_record_inhabited` meets every
hypothesis over `Sy = ℤ`. -/
theorem dfaAir_bound_identifies_record [K : DfaAirVerifierKernel St Sy Dg Proof]
    (cf : CollisionFree Dg) (hext : K.extractable)
    (stmt : Dregg2.Crypto.DfaAcceptanceAir.Statement St Sy Dg)
    (hsym : Function.Injective stmt.encSym) (proof : Proof) (hstart : stmt.d.start = stmt.initialState)
    (haccept : K.verify stmt proof = true) (record : List Sy)
    (hrec : wordCommit stmt.d stmt.encState stmt.encSym stmt.tableCommitment stmt.initialState
      record = stmt.routeCommitment) :
    ∃ rows, Satisfies stmt.d stmt.encState stmt.encSym stmt.tableCommitment stmt.initialState
        stmt.finalState stmt.routeCommitment rows ∧
      ((symbols rows = record ∧ stmt.finalState = classify stmt.d record) ∨
        (symbols rows).length ≠ record.length) := by
  obtain ⟨w, hw, hfin, rows, hsat, hsyms⟩ :=
    dfaAir_bound_verify_sound hext stmt proof hstart haccept
  refine ⟨rows, hsat, ?_⟩
  by_cases hl : (symbols rows).length = record.length
  · left
    have heq : symbols rows = record := wordCommit_injective cf _ _ _ hsym _ _ hl
      (by rw [hsyms, hw, hrec])
    exact ⟨heq, by rw [hfin, ← hsyms, heq]⟩
  · exact Or.inr hl

end Model

/-! ### The record theorem's hypotheses are jointly met over a non-trivial alphabet.

A reference kernel whose `verify` decides `Satisfies` (classically) and whose `extractable` is
`True`; the statement is the 1-row toggle run of `DfaRoutingRung2.wtG`, symbols in `ℤ` with the
identity encoding. -/

/-- The reference routing kernel: a proof is a row list, accepted iff it satisfies the AIR. -/
@[reducible] noncomputable def refKernel (hash : List ℤ → ℤ) :
    @DfaAirVerifierKernel ℤ ℤ ℤ _ (dfaPrims hash) (List (Row ℤ ℤ ℤ)) :=
  letI := dfaPrims hash
  @DfaAirVerifierKernel.mk ℤ ℤ ℤ _ (dfaPrims hash) _
    (fun stmt rows => @decide (@Satisfies ℤ ℤ ℤ _ (dfaPrims hash) stmt.d stmt.encState stmt.encSym
        stmt.tableCommitment stmt.initialState stmt.finalState stmt.routeCommitment rows)
        (Classical.dec _))
    True
    (fun _ _ rows h => ⟨rows, @of_decide_eq_true _ (Classical.dec _) h⟩)

/-- The toggle run's statement: start `0`, final `1`, seed `0`, route the genuine running hash. -/
def refStmt (hash : List ℤ → ℤ) : @Dregg2.Crypto.DfaAcceptanceAir.Statement ℤ ℤ ℤ _ (dfaPrims hash) :=
  @Dregg2.Crypto.DfaAcceptanceAir.Statement.mk ℤ ℤ ℤ _ (dfaPrims hash) (pinnedDfa 0) id id 0 0 1
    (hash [0, hash [0, 1, 1, 0]])

/-- ⚑ Every hypothesis of `dfaAir_bound_identifies_record` holds at `refHash` over `Sy = ℤ`, whose
symbol encoding is the identity (it separates `0` and `1`); the record `[1]` is identified and
classified. -/
theorem identifies_record_inhabited :
    ∃ rows, @Satisfies ℤ ℤ ℤ _ (dfaPrims refHash) (pinnedDfa 0) id id 0 0 1
        (refHash [0, refHash [0, 1, 1, 0]]) rows ∧
      ((symbols rows = [1] ∧ (1 : ℤ) = classify (pinnedDfa 0) [1]) ∨
        (symbols rows).length ≠ [1].length) := by
  exact @dfaAir_bound_identifies_record ℤ ℤ ℤ _ (dfaPrims refHash) _ (refKernel refHash)
    (collisionFree_of_injective refHash_injective) (show True from trivial) (refStmt refHash) Function.injective_id
    (wtG refHash) rfl (@decide_eq_true _ (Classical.dec _) (wtG_satisfies refHash)) [1] rfl

/-! ## §1½ — The chain binds or names a collision (deployed form, no injectivity floor).

Over `hash : List ℤ → ℤ` (the descriptor's own sponge, `compress a b = hash [a, b]`), a running
fold over the hashes of a list of preimages. Two equal-length preimage lists with one fold are
EQUAL, or the deterministic extractor `chainFind` returns a genuine `SpongeColl` pair on those two
particular chains: first along the fold (the latest step whose inputs differ while its outputs
agree), else at the first differing entry preimage. The honest prover (one list) never triggers it
(`chainFind_self`). The house shape of `Lightclient.MMR.mroot_binds_or_collides`. -/

/-- The collision extractor along two folds: walk forward; return the LAST step whose inputs differ
(the inner result wins when it is already a collision). -/
def foldFind (hash : List ℤ → ℤ) : ℤ → ℤ → List ℤ → List ℤ → List ℤ × List ℤ
  | s₁, s₂, e₁ :: r₁, e₂ :: r₂ =>
    let r := foldFind hash (hash [s₁, e₁]) (hash [s₂, e₂]) r₁ r₂
    if r.1 ≠ r.2 then r else ([s₁, e₁], [s₂, e₂])
  | _, _, _, _ => ([], [])

theorem foldFind_self (hash : List ℤ → ℤ) :
    ∀ (s : ℤ) (es : List ℤ), (foldFind hash s s es es).1 = (foldFind hash s s es es).2
  | _, [] => rfl
  | s, e :: es => by
    have ih := foldFind_self hash (hash [s, e]) es
    simp only [foldFind, ne_eq, ite_not]
    split <;> simp_all

/-- Two folds of equal length with equal results: equal seeds and entries, or a named collision. -/
theorem fold_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ (es₁ es₂ : List ℤ) (s₁ s₂ : ℤ), es₁.length = es₂.length →
      @runningFold ℤ _ (dfaPrims hash) s₁ es₁ = @runningFold ℤ _ (dfaPrims hash) s₂ es₂ →
      (s₁ = s₂ ∧ es₁ = es₂) ∨ SpongeColl hash (foldFind hash s₁ s₂ es₁ es₂)
  | [], [], _, _, _, h => Or.inl ⟨h, rfl⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | e₁ :: r₁, e₂ :: r₂, s₁, s₂, hl, h => by
    have h' : @runningFold ℤ _ (dfaPrims hash) (hash [s₁, e₁]) r₁
        = @runningFold ℤ _ (dfaPrims hash) (hash [s₂, e₂]) r₂ := h
    rcases fold_binds_or_collides hash r₁ r₂ _ _ (by simpa using hl) h' with ⟨hs, hr⟩ | hc
    · subst hr
      have hself := foldFind_self hash (hash [s₁, e₁]) r₁
      rw [hs] at hself
      by_cases hp : [s₁, e₁] = [s₂, e₂]
      · simp only [List.cons.injEq, and_true] at hp
        exact Or.inl ⟨hp.1, by rw [hp.2]⟩
      · right
        simp only [foldFind, hs, ne_eq, hself, not_true_eq_false, if_false]
        exact ⟨hp, hs⟩
    · right
      simp only [foldFind, if_pos hc.1]
      exact hc

/-- The collision extractor at the first differing preimage of two hashed lists. -/
def listFind : List (List ℤ) → List (List ℤ) → List ℤ × List ℤ
  | p₁ :: r₁, p₂ :: r₂ => if p₁ = p₂ then listFind r₁ r₂ else (p₁, p₂)
  | _, _ => ([], [])

theorem map_hash_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ (P₁ P₂ : List (List ℤ)), P₁.map hash = P₂.map hash →
      P₁ = P₂ ∨ SpongeColl hash (listFind P₁ P₂)
  | [], [], _ => Or.inl rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p₁ :: r₁, p₂ :: r₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    by_cases hp : p₁ = p₂
    · rcases map_hash_binds_or_collides hash r₁ r₂ h.2 with hr | hc
      · exact Or.inl (by rw [hp, hr])
      · right; simpa only [listFind, if_pos hp] using hc
    · right; simp only [listFind, if_neg hp]; exact ⟨hp, h.1⟩

/-- ⚑ The chain's deterministic extractor: the fold's collision if it has one, else the first
differing entry preimage. -/
def chainFind (hash : List ℤ → ℤ) (s : ℤ) (P₁ P₂ : List (List ℤ)) : List ℤ × List ℤ :=
  let r := foldFind hash s s (P₁.map hash) (P₂.map hash)
  if r.1 ≠ r.2 then r else listFind P₁ P₂

/-- ⚑ **`chain_binds_or_collides`** — two equal-length preimage lists whose seeded chains agree are
EQUAL, or `chainFind` names a genuine collision of `hash` on those two chains. -/
theorem chain_binds_or_collides (hash : List ℤ → ℤ) (s : ℤ) (P₁ P₂ : List (List ℤ))
    (hl : P₁.length = P₂.length)
    (h : @runningFold ℤ _ (dfaPrims hash) s (P₁.map hash)
      = @runningFold ℤ _ (dfaPrims hash) s (P₂.map hash)) :
    P₁ = P₂ ∨ SpongeColl hash (chainFind hash s P₁ P₂) := by
  rcases fold_binds_or_collides hash _ _ s s (by simpa using hl) h with ⟨_, he⟩ | hc
  · have hself := foldFind_self hash s (P₁.map hash)
    rcases map_hash_binds_or_collides hash P₁ P₂ he with hp | hc
    · exact Or.inl hp
    · right
      have hcf : chainFind hash s P₁ P₂ = listFind P₁ P₂ := by
        simp only [chainFind, ← he, ne_eq, hself, not_true_eq_false, if_false]
      rw [hcf]; exact hc
  · right; simp only [chainFind, if_pos hc.1]; exact hc

/-- The honest prover never triggers the extractor: one list yields an equal pair. -/
theorem chainFind_self (hash : List ℤ → ℤ) (s : ℤ) (P : List (List ℤ)) :
    (chainFind hash s P P).1 = (chainFind hash s P P).2 := by
  have hl : ∀ Q : List (List ℤ), (listFind Q Q).1 = (listFind Q Q).2 := by
    intro Q; induction Q with
    | nil => rfl
    | cons p r ih => simpa only [listFind, if_pos rfl, ↓reduceIte] using ih
  simp only [chainFind, foldFind_self, ne_eq, not_true_eq_false, if_false]
  exact hl P

/-! ## §2 — The served descriptor: the route PI is the fold of the entry-hash column. -/

section Descriptor

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- ⚑ **`route_eq_fold`** — `pi[route] = runningFold pi[table] (entry-hash column)`: the chip
lookups, the copy-forward window and the seed / B3 pins, lifted to ℤ by the chain envelope. -/
theorem route_eq_fold (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (hchain : DfaChainCanon t)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2)) :
    t.pub PI_ROUTE = @runningFold ℤ _ (dfaPrims hash) (t.pub PI_TABLE) (entryHashes (traceRows t)) := by
  letI := dfaPrims hash
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hne_tr : traceRows t ≠ [] := by
    simp only [traceRows, ne_eq, List.map_eq_nil_iff]; exact hne
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
  have hb3Z : (t.rows[t.rows.length - 1]'hlt) RUNNING_HASH = t.pub PI_ROUTE :=
    eq_of_modEq_of_canon hb3 ((hchain.1 _ hlt).2).1 ((hchain.1 _ hlt).2).2
      hchain.2.2.1 hchain.2.2.2
  have h1 : (mkRow (t.rows.getLast hne)).running = t.pub PI_ROUTE := by
    show (t.rows.getLast hne) RUNNING_HASH = t.pub PI_ROUTE
    rw [List.getLast_eq_getElem hne]; exact hb3Z
  rw [← h1]; exact hrun_last

/-- The commitment of a word under the served descriptor's own hash (toggle table, identity
encodings). -/
def routeOf (hash : List ℤ → ℤ) (tc q₀ : ℤ) (w : List ℤ) : ℤ :=
  @wordCommit ℤ ℤ ℤ _ (dfaPrims hash) (pinnedDfa q₀) id id tc q₀ w

/-- Rows whose entry hashes ARE the run entries of `w` from `q` read `w`, and the last row's `next`
is `w`'s classification from `q`. Pure: the chain pins every triple (`compressN` injectivity). -/
theorem rows_of_entries (cf : @CollisionFree ℤ _ (dfaPrims hash)) (q₀ : ℤ) :
    ∀ (l : List Assignment) (q : ℤ) (w : List ℤ),
    (∀ a ∈ l, a ENTRY_HASH = hash [a CURRENT, a SYMBOL, a NEXT, a ZERO_LANE]) →
    l.map (fun a => a ENTRY_HASH) = @runEntries ℤ ℤ ℤ _ (dfaPrims hash) (pinnedDfa q₀) id id q w →
    l.map (fun a => a SYMBOL) = w ∧
      ∀ hne : l ≠ [], (l.getLast hne) NEXT = classifyFrom (pinnedDfa q₀) q w
  | [], _, [], _, _ => ⟨rfl, fun h => absurd rfl h⟩
  | [], _, _ :: _, _, h => by simp [runEntries] at h
  | _ :: _, _, [], _, h => by simp [runEntries] at h
  | a :: rest, q, y :: ys, hent, h => by
    letI := dfaPrims hash
    simp only [List.map_cons, runEntries, List.cons.injEq] at h
    obtain ⟨hh, ht⟩ := h
    rw [hent a List.mem_cons_self] at hh
    have hl : [a CURRENT, a SYMBOL, a NEXT, a ZERO_LANE] = [q, y, toggleStep q y, 0] :=
      cf.compressN_inj _ _ hh
    simp only [List.cons.injEq] at hl
    obtain ⟨hcur, hsym, hnext, _⟩ := hl
    obtain ⟨ih1, ih2⟩ := rows_of_entries cf q₀ rest (toggleStep q y) ys
      (fun b hb => hent b (List.mem_cons_of_mem _ hb)) ht
    refine ⟨by simp [hsym, ih1], fun _ => ?_⟩
    cases rest with
    | nil =>
      cases ys with
      | nil => simp only [List.getLast_singleton, classifyFrom_cons, classifyFrom_nil]
               rw [hnext]; rfl
      | cons _ _ => simp at ih1
    | cons b bs =>
      rw [List.getLast_cons (by simp), ih2 (by simp), classifyFrom_cons]
      rfl

/-- ⚑ **`dfaRouting_bound` — THE CONTENT-BOUND THEOREM for the served routing descriptor.** For a
record `w` whose commitment is the public route commitment, and of the trace's length, a satisfying
trace READS `w` and its public final state is `w`'s classification. -/
theorem dfaRouting_bound
    (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (hcanon : DfaTraceCanon t) (hchain : DfaChainCanon t)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2))
    (cf : @CollisionFree ℤ _ (dfaPrims hash))
    (w : List ℤ) (hc : t.pub PI_ROUTE = routeOf hash (t.pub PI_TABLE) (t.pub PI_INITIAL) w)
    (hlen : t.rows.length = w.length) :
    symbols (traceRows t) = w ∧
      t.pub PI_FINAL = classify (pinnedDfa (t.pub PI_INITIAL)) w := by
  letI := dfaPrims hash
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hfold := route_eq_fold hsat hne hchain hchip hwire
  have hEH : entryHashes (traceRows t)
      = runEntries (pinnedDfa (t.pub PI_INITIAL)) id id (t.pub PI_INITIAL) w :=
    fold_inj cf _ _ (by simp [entryHashes, traceRows, runEntries_length, hlen]) (t.pub PI_TABLE)
      (by rw [← hfold, hc]; rfl)
  have hent : ∀ a ∈ t.rows, a ENTRY_HASH = hash [a CURRENT, a SYMBOL, a NEXT, a ZERO_LANE] := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact entry_eq hsat hchip hwire hi
  have hmap : t.rows.map (fun a => a ENTRY_HASH)
      = runEntries (pinnedDfa (t.pub PI_INITIAL)) id id (t.pub PI_INITIAL) w := by
    rw [← hEH]; simp [entryHashes, traceRows, mkRow]
  obtain ⟨hsyms, hlast⟩ := rows_of_entries cf (t.pub PI_INITIAL) t.rows _ w hent hmap
  refine ⟨by rw [symbols_traceRows]; exact hsyms, ?_⟩
  have hb2 := piLast_forces hsat hne mem_b2FinalPin
  rw [envAt_loc hlt] at hb2
  have hcN := (hcanon.1 _ hlt).2.2
  have hfZ : (t.rows[t.rows.length - 1]'hlt) NEXT = t.pub PI_FINAL :=
    eq_of_modEq_of_canon hb2 hcN.1 hcN.2 hcanon.2.2.1 hcanon.2.2.2
  rw [← hfZ, ← List.getLast_eq_getElem hne, hlast hne]
  rfl

/-- ⚑ **`dfaRouting_bound_accepts`** — the whole-run corollary: if the public final state is
accepting, the record's run from the public initial state is an accepting run of the pinned DFA. -/
theorem dfaRouting_bound_accepts
    (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (hcanon : DfaTraceCanon t) (hchain : DfaChainCanon t)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2))
    (cf : @CollisionFree ℤ _ (dfaPrims hash))
    (w : List ℤ) (hc : t.pub PI_ROUTE = routeOf hash (t.pub PI_TABLE) (t.pub PI_INITIAL) w)
    (hlen : t.rows.length = w.length)
    (hacc : (pinnedDfa (t.pub PI_INITIAL)).accepts (t.pub PI_FINAL)) :
    (pinnedDfa (t.pub PI_INITIAL)).accepts (classify (pinnedDfa (t.pub PI_INITIAL)) w) := by
  rw [← (dfaRouting_bound hsat hne hcanon hchain hchip hwire cf w hc hlen).2]; exact hacc

/-! ### The deployed form: bound, or a named collision of `hash` (no `CollisionFree`). -/

/-- The entry preimage of a routing row. -/
def rowPre (a : Assignment) : List ℤ := [a CURRENT, a SYMBOL, a NEXT, a ZERO_LANE]

/-- The entry preimages of `w`'s toggle run from `q`. -/
def runPre : ℤ → List ℤ → List (List ℤ)
  | _, [] => []
  | q, y :: ys => [q, y, toggleStep q y, 0] :: runPre (toggleStep q y) ys

theorem runPre_length : ∀ (q : ℤ) (w : List ℤ), (runPre q w).length = w.length
  | _, [] => rfl
  | q, _ :: ys => by simp [runPre, runPre_length _ ys]

theorem runEntries_eq_map (hash : List ℤ → ℤ) (q₀ : ℤ) : ∀ (q : ℤ) (w : List ℤ),
    @runEntries ℤ ℤ ℤ _ (dfaPrims hash) (pinnedDfa q₀) id id q w = (runPre q w).map hash
  | _, [] => rfl
  | q, y :: ys => congrArg₂ List.cons rfl (runEntries_eq_map hash q₀ (toggleStep q y) ys)

/-- Rows whose entry preimages ARE `w`'s run preimages read `w`, and the last row's `next` is `w`'s
classification. No hash at all. -/
theorem rows_of_pre (q₀ : ℤ) : ∀ (l : List Assignment) (q : ℤ) (w : List ℤ),
    l.map rowPre = runPre q w →
    l.map (fun a => a SYMBOL) = w ∧
      ∀ hne : l ≠ [], (l.getLast hne) NEXT = classifyFrom (pinnedDfa q₀) q w
  | [], _, [], _ => ⟨rfl, fun h => absurd rfl h⟩
  | [], _, _ :: _, h => by simp [runPre] at h
  | _ :: _, _, [], h => by simp [runPre] at h
  | a :: rest, q, y :: ys, h => by
    simp only [List.map_cons, runPre, List.cons.injEq, rowPre] at h
    obtain ⟨⟨hcur, hsym, hnext, _⟩, ht⟩ := h
    obtain ⟨ih1, ih2⟩ := rows_of_pre q₀ rest (toggleStep q y) ys ht
    refine ⟨by simp [hsym, ih1], fun _ => ?_⟩
    cases rest with
    | nil =>
      cases ys with
      | nil => simp only [List.getLast_singleton, classifyFrom_cons, classifyFrom_nil]
               rw [hnext]; rfl
      | cons _ _ => simp at ih1
    | cons b bs =>
      rw [List.getLast_cons (by simp), ih2 (by simp), classifyFrom_cons]
      rfl

/-- The last row's `next` is the public final state (B2, lifted). -/
theorem final_pin (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (hcanon : DfaTraceCanon t) :
    (t.rows.getLast hne) NEXT = t.pub PI_FINAL := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hb2 := piLast_forces hsat hne mem_b2FinalPin
  rw [envAt_loc hlt] at hb2
  have hcN := (hcanon.1 _ hlt).2.2
  rw [List.getLast_eq_getElem hne]
  exact eq_of_modEq_of_canon hb2 hcN.1 hcN.2 hcanon.2.2.1 hcanon.2.2.2

/-- The extractor for one trace against one record: the trace's entry preimages against the
record's run preimages, along the chain seeded at `pi[table]`. -/
def boundFind (hash : List ℤ → ℤ) (t : VmTrace) (w : List ℤ) : List ℤ × List ℤ :=
  chainFind hash (t.pub PI_TABLE) (t.rows.map rowPre) (runPre (t.pub PI_INITIAL) w)

/-- ⚑ **`dfaRouting_bound_or_collides` — the content-bound theorem in its deployed form.** For a
record of the trace's length whose commitment is the public route, a satisfying trace READS the
record and is classified to it, OR `boundFind` returns a genuine collision of `hash` on the trace's
chain and the record's. No injectivity hypothesis. -/
theorem dfaRouting_bound_or_collides
    (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (hcanon : DfaTraceCanon t) (hchain : DfaChainCanon t)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2))
    (w : List ℤ) (hc : t.pub PI_ROUTE = routeOf hash (t.pub PI_TABLE) (t.pub PI_INITIAL) w)
    (hlen : t.rows.length = w.length) :
    (symbols (traceRows t) = w ∧
      t.pub PI_FINAL = classify (pinnedDfa (t.pub PI_INITIAL)) w) ∨
      SpongeColl hash (boundFind hash t w) := by
  have hfold := route_eq_fold hsat hne hchain hchip hwire
  have hcol : entryHashes (traceRows t) = (t.rows.map rowPre).map hash := by
    simp only [entryHashes, traceRows, List.map_map]
    apply List.map_congr_left
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact entry_eq hsat hchip hwire hi
  have hrun : routeOf hash (t.pub PI_TABLE) (t.pub PI_INITIAL) w
      = @runningFold ℤ _ (dfaPrims hash) (t.pub PI_TABLE)
          ((runPre (t.pub PI_INITIAL) w).map hash) := by
    simp only [routeOf, wordCommit]; rw [runEntries_eq_map]
  rcases chain_binds_or_collides hash (t.pub PI_TABLE) (t.rows.map rowPre)
      (runPre (t.pub PI_INITIAL) w) (by simp [runPre_length, hlen])
      (by rw [← hcol, ← hfold, hc, hrun]) with hP | hcoll
  · left
    obtain ⟨hsyms, hlast⟩ := rows_of_pre (t.pub PI_INITIAL) t.rows _ w hP
    refine ⟨by rw [symbols_traceRows]; exact hsyms, ?_⟩
    rw [← final_pin hsat hne hcanon, hlast hne]
    rfl
  · exact Or.inr hcoll

/-! ### The bound acceptance check (codex round 4 item 5).

`UnboundAccepts` is the record-ignoring acceptance (the descriptor is satisfied; Rung 2's conclusion
is about the word read off the trace, so the record is not consulted). `BoundAccepts` adds the two
record checks the content-bound theorem consumes: the record opens the public route, and the record
has the trace's length. -/

def UnboundAccepts (hash : List ℤ → ℤ) (t : VmTrace) (_w : List ℤ) : Prop :=
  Satisfied2 hash dfaRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] t

def BoundAccepts (hash : List ℤ → ℤ) (t : VmTrace) (w : List ℤ) : Prop :=
  Satisfied2 hash dfaRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] t ∧
    t.pub PI_ROUTE = routeOf hash (t.pub PI_TABLE) (t.pub PI_INITIAL) w ∧
    t.rows.length = w.length

/-- What `BoundAccepts` buys (with the envelopes): the record is read and classified, or a named
collision. -/
theorem boundAccepts_sound {w' : List ℤ} (h : BoundAccepts hash t w')
    (hne : t.rows ≠ []) (hcanon : DfaTraceCanon t) (hchain : DfaChainCanon t)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf .poseidon2)) :
    (symbols (traceRows t) = w' ∧
      t.pub PI_FINAL = classify (pinnedDfa (t.pub PI_INITIAL)) w') ∨
      SpongeColl hash (boundFind hash t w') :=
  dfaRouting_bound_or_collides h.1 hne hcanon hchain hchip hwire w' h.2.1 h.2.2

end Descriptor

/-! ## §3 — Non-vacuity: the bound theorem fires on the genuine witness. -/

/-- The genuine 1-row witness opens the commitment of its own word `[1]`. -/
theorem wt_route_is_wordCommit :
    (wtTrace refHash).pub PI_ROUTE
      = routeOf refHash ((wtTrace refHash).pub PI_TABLE) ((wtTrace refHash).pub PI_INITIAL) [1] := rfl

/-- ⚑ The content-bound theorem FIRES: the witness reads `[1]` and is classified to `1`. -/
theorem wt_bound_fires :
    symbols (traceRows (wtTrace refHash)) = [1] ∧
      (wtTrace refHash).pub PI_FINAL = classify (pinnedDfa ((wtTrace refHash).pub PI_INITIAL)) [1] :=
  dfaRouting_bound (wtTrace_satisfied2 refHash) (by simp [wtTrace]) (wtTrace_dfaCanon refHash)
    (wtTrace_chainCanon refHash refHash_route_canon) (wtTf_chipSound refHash)
    (wtTf_narrow_wire refHash) (collisionFree_of_injective refHash_injective) [1]
    wt_route_is_wordCommit rfl

/-! ## §4 — The falsifier: the record-ignoring acceptance meets the unbound shape and fails the
bound one. -/

/-- The unbound shape HOLDS on the witness: `Satisfied2`, and Rung 2's conclusion about the word
read off the trace. -/
theorem splice_meets_unbound :
    Satisfied2 refHash dfaRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] (wtTrace refHash) ∧
    (wtTrace refHash).pub PI_FINAL
      = classify (pinnedDfa ((wtTrace refHash).pub PI_INITIAL))
          (symbols (traceRows (wtTrace refHash))) := ⟨wtTrace_satisfied2 refHash, refWitness_fires⟩

/-- Read as a statement about the record `[0]`, that acceptance is FALSE: `[0]` classifies to `0`,
the public final state is `1`. -/
theorem splice_false_of_record :
    (wtTrace refHash).pub PI_FINAL
      ≠ classify (pinnedDfa ((wtTrace refHash).pub PI_INITIAL)) [0] := by decide

/-- The record-opening equality fails for `[0]`: the public route commitment is not its
commitment. -/
theorem splice_route_mismatch :
    (wtTrace refHash).pub PI_ROUTE
      ≠ routeOf refHash ((wtTrace refHash).pub PI_TABLE) ((wtTrace refHash).pub PI_INITIAL) [0] := by
  rw [wt_route_is_wordCommit]
  intro h
  have := @wordCommit_injective ℤ ℤ ℤ _ (dfaPrims refHash)
    (collisionFree_of_injective refHash_injective) _ id id Function.injective_id _ _ [1] [0] rfl h
  simp at this

/-- **The separation**: the bound conclusion cannot hold for the record `[0]` on this trace, while
the unbound one holds. -/
theorem splice_fails_bound :
    ¬ (symbols (traceRows (wtTrace refHash)) = [0] ∧
      (wtTrace refHash).pub PI_FINAL
        = classify (pinnedDfa ((wtTrace refHash).pub PI_INITIAL)) [0]) :=
  fun h => splice_false_of_record h.2

/-- The bound acceptance ACCEPTS the honest record `[1]`. -/
theorem wt_boundAccepts : BoundAccepts refHash (wtTrace refHash) [1] :=
  ⟨wtTrace_satisfied2 refHash, rfl, rfl⟩

/-- ⚑ **`splice_separation`** — one trace, one record: the record-ignoring acceptance ACCEPTS
`(wtTrace, [0])`, the bound acceptance REFUSES it, and the claim about `[0]` is false. -/
theorem splice_separation :
    UnboundAccepts refHash (wtTrace refHash) [0] ∧ ¬ BoundAccepts refHash (wtTrace refHash) [0] ∧
      (wtTrace refHash).pub PI_FINAL
        ≠ classify (pinnedDfa ((wtTrace refHash).pub PI_INITIAL)) [0] :=
  ⟨wtTrace_satisfied2 refHash, fun h => splice_route_mismatch h.2.1, splice_false_of_record⟩

/-- The deployed-form theorem fires on the witness with no injectivity hypothesis; its collision
branch is closed here only because `refHash` is injective. -/
theorem wt_bound_or_collides :
    (symbols (traceRows (wtTrace refHash)) = [1] ∧
      (wtTrace refHash).pub PI_FINAL
        = classify (pinnedDfa ((wtTrace refHash).pub PI_INITIAL)) [1]) ∨
      SpongeColl refHash (boundFind refHash (wtTrace refHash) [1]) :=
  dfaRouting_bound_or_collides (wtTrace_satisfied2 refHash) (by simp [wtTrace])
    (wtTrace_dfaCanon refHash) (wtTrace_chainCanon refHash refHash_route_canon)
    (wtTf_chipSound refHash) (wtTf_narrow_wire refHash) [1] wt_route_is_wordCommit rfl

/-- The honest trace never triggers the extractor: its collision disjunct is false by
`chainFind_self`, which uses no property of the hash. -/
theorem wt_no_collision : ¬ SpongeColl refHash (boundFind refHash (wtTrace refHash) [1]) :=
  fun h => h.1 (by
    have : (wtTrace refHash).rows.map rowPre = runPre ((wtTrace refHash).pub PI_INITIAL) [1] := rfl
    simp only [boundFind, this]
    exact chainFind_self _ _ _)

/-! ## §5 — axiom tripwires. -/

#assert_all_clean [runEntries_length, entryHashes_eq_runEntries, exists_getLast',
  route_eq_wordCommit, runEntries_inj, wordCommit_injective, dfaAir_bound_verify_sound,
  dfaAir_bound_identifies_record, route_eq_fold, rows_of_entries, dfaRouting_bound,
  dfaRouting_bound_accepts, wt_route_is_wordCommit, wt_bound_fires, splice_meets_unbound,
  splice_false_of_record, splice_route_mismatch, splice_fails_bound, refKernel,
  identifies_record_inhabited, foldFind_self, fold_binds_or_collides, map_hash_binds_or_collides,
  chain_binds_or_collides, chainFind_self, runPre_length, runEntries_eq_map, rows_of_pre, final_pin,
  dfaRouting_bound_or_collides, boundAccepts_sound, wt_boundAccepts, splice_separation,
  wt_bound_or_collides, wt_no_collision]

end Dregg2.Circuit.Emit.DfaRoutingChainBound
