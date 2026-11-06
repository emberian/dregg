/-
# Dregg2.Crypto.Dfa — §8 discharge: DFA structural-match acceptance.

Discharges `WitnessedPredicateKind::Dfa`. Deployed carrier (corrected 2026-07-16): the
`dfa-routing-toggle-2state::poseidon2-v1` descriptor — dispatched at
`circuit/src/descriptor_by_name.rs` (`PredicateKind::Dfa`), DSL builder
`circuit/src/dsl/dfa_routing.rs`, Lean emit `Circuit/Emit/DfaRoutingEmit.lean`. The originally
cited `dsl/circuit.rs` builder `dfa_lookup_descriptor` was DELETED with the hand-STARK engine;
this module models that retired builder's simple form — the structural core the deployed routing
descriptor extends with a rolling Poseidon2 route commitment. The statement: a trace of
automaton states threaded by a transition relation `δ` starts in the initial state and ends in an
accepting state. Per-step `Lookup` membership, `Transition` chaining, and boundary `PiBinding`s.

    dfa_bridge       : Satisfies dfaCircuit (q₀, accept, trace) ↔ DfaAccepts δ q₀ accept trace
    dfa_verify_sound : verify accepts → DfaAccepts …  (derived off the bridge + `extractable`)
    dfa_dial_wired   : dial at `fullDisclosure` (DFA structure and trace are public)

The DFA gadget is pure structural matching — no `compress`/hash, no primitive seam. Crypto residue:
the STARK `extractable` carrier only.

⚑ **THE STATEMENT NOW NAMES THE WORD (2026-11-05; `zkml-research/docs/CERTIFICATES.md` §0.1, L0, P6).**
`Statement` holds `δ, q₀, accept` and NOTHING else — no input, no commitment — so `dfa_verify_sound`
concludes `∃ trace, DfaAccepts …`, a sentence about the AUTOMATON that never mentions which record was
read. For a complement automaton (the absence use) it holds for nearly every proof, and an accepting
run over a benign word discharges it for ANY record: the zero-work "splice". Layer B′ below repairs it:
`BoundStatement` carries a content commitment `c`, `DfaBoundVerifierKernel.extract` delivers a run
WHOSE WORD COMMITS TO `c`, and `dfa_bound_verify_sound` concludes
`∃ w, commit w = stmt.c ∧ ∃ trace, DfaAccepts … trace ∧ traceWord trace = w`. The dial wiring (Layer C)
is re-pointed to the bound kernel. The unbound `DfaVerifierKernel`/`dfa_verify_sound` are RETAINED,
unchanged, as the subject of `PremiseInhabitabilityConclusionAxis` §5 and of the falsifier
`Reference.splice_meets_unbound` / `Reference.splice_fails_bound`: the SAME acceptance test (a run
checked against the automaton, record ignored) meets the unbound extract shape and refutes the bound
one. That pair is the exhibited separation; it is what the repair buys.
-/
import Dregg2.Crypto.Chain
import Dregg2.Crypto.Primitives
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.Dfa

open Dregg2.Crypto

universe u

/-! ## The DFA relation (the statement algebra) — a valid accepting run.

We model the automaton over abstract `State`/`Sym` carriers. A step is a `(state, sym, next)` triple;
the transition relation `δ : State → Sym → State → Prop` is the membership predicate of the real
`Lookup` transition table (the retired builder's `dfa_lookup_table` — deleted with the hand-STARK
engine; the table's entries ARE the `δ` graph, which the deployed routing descriptor enforces via
its transition-interpolant gate). A run is a list of steps; it ACCEPTS iff each step is a valid `δ` transition, consecutive
steps chain (`next` of one is `state` of the following), the first `state` is the initial state `q₀`,
and the final `next` is accepting (`accept : State → Prop`). This is exactly the `Lookup` + `Transition`
+ boundary `PiBinding`s the AIR enforces. -/

variable {State Sym : Type u}

/-- A single DFA step: the current `state`, the input `sym`bol read, and the `next` state. Mirrors a
trace row `[state, byte, next_state]` (the retired `dfa_lookup_descriptor` builder's row shape). -/
structure Step (State Sym : Type u) where
  /-- The state entering this step (trace column `state`). -/
  state : State
  /-- The input symbol read (trace column `byte`). -/
  sym : Sym
  /-- The state after the transition (trace column `next_state`). -/
  next : State
  deriving Repr

/-- **Each step is a valid transition** under `δ`: `δ step.state step.sym step.next`. This is the
`Lookup` membership — `(state, byte, next_state)` is an entry of the transition table, abstracted as
the relation `δ` exactly as the table lookup routes (`circuit.rs` DFA `Lookup` constraint). -/
def stepValid (δ : State → Sym → State → Prop) (s : Step State Sym) : Prop :=
  δ s.state s.sym s.next

/-- **Consecutive steps chain** (`Transition`): each step's `next` equals the following step's
`state`. Stated over the step list. DEFINITIONALLY the generic `Hypergraph.chain`
(`Crypto/Chain.lean`) at the step-chaining relation `fun a b => b.state = a.next` (=
`DfaAsCert.delta`) — the same structural recursion, not a re-roll. -/
def chained : List (Step State Sym) → Prop :=
  Hypergraph.chain fun a b => b.state = a.next

/-- **`DfaAccepts δ q₀ accept trace`** — the DFA acceptance STATEMENT: the run is NON-EMPTY, every step
is a valid `δ` transition, the steps chain, the first step starts in the initial state `q₀`, and the
last step's `next` is accepting. This is the relation the verifier's accepting bit must certify — a
valid accepting run of the automaton. -/
def DfaAccepts (δ : State → Sym → State → Prop) (q₀ : State) (accept : State → Prop)
    (trace : List (Step State Sym)) : Prop :=
  ∃ first last,
    trace.head? = some first ∧
    trace.getLast? = some last ∧
    first.state = q₀ ∧                              -- PiBinding: first state = initial
    accept last.next ∧                              -- PiBinding: final next-state accepts
    (∀ s ∈ trace, stepValid δ s) ∧                  -- Lookup: every step a valid transition
    chained trace                                   -- Transition: the run chains

/-! ## `CircuitIR` — the DFA AIR (per-step `Lookup` + `Transition` + boundary), no primitive seam.

Mirrors the retired `dfa_lookup_descriptor` builder (deleted with the hand-STARK engine; see the
header note): the trace is the row list, each row a `Step`. The
constraints: `Lookup` (each row's `(state, sym, next)` is a transition-table member, i.e. `δ`-valid),
`Transition` (chaining), and the two boundary `PiBinding`s (first state = `q₀`, final next accepts).
NO `compress`/hash here — the DFA gadget is pure structural matching, so NO primitive seam. We carry
the `Lookup` table abstractly as the relation `δ` (the table's membership predicate), which is exactly
what the lookup constraint enforces; this is the documented `Lookup`/`Gated` abstraction the task
calls for (added LOCALLY as a `δ` relation rather than editing the shared `CircuitIR`). -/

/-- **The DFA circuit IR** — the trace: the list of `Step` rows. -/
structure CircuitIR (State Sym : Type u) where
  /-- The trace rows (one per automaton step). -/
  trace : List (Step State Sym)
  deriving Repr

/-- **`Satisfies δ q₀ accept circuit`** — the full DFA AIR check: the trace is non-empty, every row's
`(state, sym, next)` is a valid `δ` transition (the `Lookup` membership), the rows chain (the
`Transition` constraint), and the two boundaries hold (first state = `q₀`, final next accepts). This
is the conjunction the retired `dfa_lookup_descriptor` enforced — IDENTICAL in shape to `DfaAccepts` (the IR and
the statement coincide; the bridge below is then largely an unfolding, which is honest: the DFA AIR's
satisfiability IS acceptance, with the `Lookup` abstracted as `δ`). -/
def Satisfies (δ : State → Sym → State → Prop) (q₀ : State) (accept : State → Prop)
    (circuit : CircuitIR State Sym) : Prop :=
  ∃ first last,
    circuit.trace.head? = some first ∧
    circuit.trace.getLast? = some last ∧
    first.state = q₀ ∧
    accept last.next ∧
    (∀ s ∈ circuit.trace, stepValid δ s) ∧
    chained circuit.trace

/-! ## The bridge — `Satisfies ↔ DfaAccepts`, FULLY proven (NO primitive seam).

Both directions. The DFA AIR's satisfiability is EXACTLY a valid accepting run: the `Lookup`
membership IS per-step `δ`-validity, the `Transition` IS chaining, and the boundary `PiBinding`s ARE
the initial/accept conditions. There is NO `compress`/hash anywhere — the DFA gadget is pure
structural matching — so NO primitive seam. -/

/-- **`dfa_sound` (the `→` half).** A satisfying trace PROVES acceptance: the per-step `Lookup`
validity, the chaining, and the boundary conditions are exactly `DfaAccepts`. Fully proved, no
crypto. -/
theorem dfa_sound (δ : State → Sym → State → Prop) (q₀ : State) (accept : State → Prop)
    (circuit : CircuitIR State Sym) (h : Satisfies δ q₀ accept circuit) :
    DfaAccepts δ q₀ accept circuit.trace := h

/-- **`dfa_complete` (the `←` half).** A genuine accepting run has a satisfying trace: package the run
as the circuit's trace; the `Lookup`/`Transition`/boundary checks are exactly the run's conditions. -/
theorem dfa_complete (δ : State → Sym → State → Prop) (q₀ : State) (accept : State → Prop)
    (trace : List (Step State Sym)) (h : DfaAccepts δ q₀ accept trace) :
    ∃ circuit : CircuitIR State Sym, Satisfies δ q₀ accept circuit :=
  ⟨⟨trace⟩, h⟩

/-- **`dfa_bridge`** — the DFA AIR's satisfiability is exactly a valid accepting run of the automaton.
Soundness: per-step `Lookup` validity + chaining + boundaries are `DfaAccepts` (`dfa_sound`).
Completeness: a genuine accepting run gives a satisfying trace (`dfa_complete`).
No `compress` anywhere — no primitive seam. Crypto residue: `extractable`, consumed by
`dfa_verify_sound`. -/
theorem dfa_bridge (δ : State → Sym → State → Prop) (q₀ : State) (accept : State → Prop)
    (trace : List (Step State Sym)) :
    -- SOUNDNESS: every satisfying trace over `trace` certifies an accepting run.
    (∀ circuit : CircuitIR State Sym, circuit.trace = trace →
        Satisfies δ q₀ accept circuit → DfaAccepts δ q₀ accept trace)
    ∧
    -- COMPLETENESS: a genuine accepting run gives a satisfying trace.
    (DfaAccepts δ q₀ accept trace → ∃ circuit : CircuitIR State Sym, Satisfies δ q₀ accept circuit) :=
  ⟨fun circuit hc hsat => hc ▸ dfa_sound δ q₀ accept circuit hsat,
   dfa_complete δ q₀ accept trace⟩

-- Tripwires: both bridge directions are kernel-clean. No `compress`/hash — pure structural matching.
#assert_axioms dfa_sound
#assert_axioms dfa_complete
#assert_axioms dfa_bridge

/-! ## Layer B — the DFA `VerifierKernel`: `verify` + carrier + DERIVED `verify_sound`.

Mirrors the prior kernels. `verify` is the §8 oracle over the disclosed statement; `extractable`
(STARK soundness) gives "accept ⇒ a satisfying trace exists"; `dfa_verify_sound` is DERIVED off the
bridge's soundness half. The statement/proof are at universe 0 (the registry/dial machinery lives
there), so the kernel is over `Type`-level `State`/`Sym`. -/

/-- **The disclosed DFA statement** — the public inputs the verifier sees: the transition relation
`δ` (the public automaton, as the lookup table), the initial state `q₀`, and the accept predicate. At
the `fullDisclosure` floor the entire automaton structure is public. -/
structure Statement (State Sym : Type) where
  /-- The transition relation (the public lookup table's membership predicate). -/
  δ : State → Sym → State → Prop
  /-- The initial state. -/
  q₀ : State
  /-- The accept predicate. -/
  accept : State → Prop

/-- **Layer B — the DFA `VerifierKernel`.** The §8 `verify` oracle over the disclosed automaton +
trace, and the STARK `extractable` carrier. `extract` unpacks `extractable` to its operational
content: an accepted proof witnesses a satisfying DFA trace for the disclosed statement — the
existence FRI/Fiat-Shamir soundness delivers. NO `binding`/`compress` carriers (no commitment, no
hash): the only assumption is STARK extractability. -/
class DfaVerifierKernel (State Sym : Type) (Proof : Type) where
  /-- **The §8 verify oracle** (`stark::verify` for the DFA-lookup AIR): does `proof` discharge the
  disclosed automaton statement? -/
  verify : Statement State Sym → Proof → Bool
  /-- **CARRIER — STARK extractability/soundness** (FRI + Fiat-Shamir): accept ⇒ a satisfying trace
  exists. A `Prop`; never proved. -/
  extractable : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying DFA trace for the disclosed
  automaton. The named form the bridge composes with — STARK soundness. -/
  extract : extractable →
    ∀ (stmt : Statement State Sym) (proof : Proof), verify stmt proof = true →
      ∃ circuit : CircuitIR State Sym, Satisfies stmt.δ stmt.q₀ stmt.accept circuit

variable {Proof : Type}

/-- **`dfa_verify_sound`** — given `extractable`, an accepted DFA proof proves a valid accepting run
exists: `verify stmt proof = true  →  ∃ trace, DfaAccepts stmt.δ stmt.q₀ stmt.accept trace`.
Derived by composing `extract` with `dfa_bridge`'s soundness half; never assumed. -/
theorem dfa_verify_sound {State Sym : Type} [K : DfaVerifierKernel State Sym Proof]
    (hext : K.extractable) (stmt : Statement State Sym) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ trace : List (Step State Sym), DfaAccepts stmt.δ stmt.q₀ stmt.accept trace := by
  obtain ⟨circuit, hsat⟩ := K.extract hext stmt proof haccept
  exact ⟨circuit.trace, dfa_sound stmt.δ stmt.q₀ stmt.accept circuit hsat⟩

#assert_axioms dfa_verify_sound

/-! ## Layer B′ — THE CONTENT-BOUND statement and kernel (law L0: the statement binds content).

`dfa_verify_sound` is honest about what the unbound kernel delivers, and that is the problem: its
conclusion is a property of the public automaton, not of any record. The bound kernel's `extract`
hands back a satisfying trace together with the fact that the trace's WORD commits to the
statement's `c`. Binding of the commitment (two words behind one `c` agree) is deliberately NOT
assumed here — it is the separate, advantage-shaped hypothesis a consumer adds when it conjoins two
certificates over one `c` (CERTIFICATES.md P1/L1); soundness of ONE certificate needs only that the
extracted word opens `c`. -/

/-- The word a trace reads: its `sym` column, in order. -/
def traceWord (trace : List (Step State Sym)) : List Sym := trace.map (·.sym)

@[simp] theorem traceWord_nil : traceWord ([] : List (Step State Sym)) = [] := rfl
@[simp] theorem traceWord_cons (s : Step State Sym) (rest : List (Step State Sym)) :
    traceWord (s :: rest) = s.sym :: traceWord rest := rfl

/-- A content scheme: the ONLY cryptographic object the bound statement names. `commit` is total
and abstract. (The identity scheme `⟨id⟩` is a legitimate instance — perfectly binding, not hiding —
and is what the falsifier below uses.) -/
structure ContentScheme (Sym D : Type) where
  /-- The commitment to a word. -/
  commit : List Sym → D

/-- **The content-bound DFA statement**: the disclosed automaton PLUS the commitment `c` of the word
the accepted run must read. -/
structure BoundStatement (State Sym D : Type) extends Statement State Sym where
  /-- The content commitment of the input word. -/
  c : D

/-- **Layer B′ — the content-bound `VerifierKernel`.** As `DfaVerifierKernel`, but `extract` delivers
a satisfying trace WHOSE WORD COMMITS TO THE STATEMENT'S `c`. In the deployed routing AIR
(`DfaAcceptanceAir.lean`) this is the hash chain `routeCommitment` over the `(state, sym, next)`
rows; here it is abstract in the scheme `S`. -/
class DfaBoundVerifierKernel (State Sym D : Type) (S : ContentScheme Sym D) (Proof : Type)
    (Input : Type := BoundStatement State Sym D) where
  /-- Interpret executable public input data as the semantic statement. Separating presentation
  from meaning permits Boolean transition tables without deciding arbitrary propositions. -/
  interpret : Input → BoundStatement State Sym D
  /-- The §8 verify oracle over the public input presentation. -/
  verify : Input → Proof → Bool
  /-- CARRIER — extraction/soundness. Assumed for a STARK; proved for the reference checker. -/
  extractable : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying trace whose word commits to
  the disclosed `c`. -/
  extract : extractable →
    ∀ (input : Input) (proof : Proof), verify input proof = true →
      ∃ circuit : CircuitIR State Sym,
        Satisfies (interpret input).δ (interpret input).q₀ (interpret input).accept circuit
          ∧ S.commit (traceWord circuit.trace) = (interpret input).c

/-- ⚑ **`dfa_bound_verify_sound`** — the repaired soundness statement. Given `extractable`, an accepted
proof of the bound statement proves: SOME WORD `w` commits to the disclosed `c`, and there is an
accepting run of the disclosed automaton that READS `w`. Derived off `extract` and `dfa_sound`. -/
theorem dfa_bound_verify_sound {State Sym D Input : Type} {S : ContentScheme Sym D}
    [K : DfaBoundVerifierKernel State Sym D S Proof Input]
    (hext : K.extractable (Input := Input)) (stmt : Input) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ w : List Sym, S.commit w = (K.interpret stmt).c ∧
      ∃ trace : List (Step State Sym),
        DfaAccepts (K.interpret stmt).δ (K.interpret stmt).q₀ (K.interpret stmt).accept trace ∧ traceWord trace = w := by
  obtain ⟨circuit, hsat, hc⟩ := K.extract hext stmt proof haccept
  exact ⟨traceWord circuit.trace, hc, circuit.trace,
    dfa_sound (K.interpret stmt).δ (K.interpret stmt).q₀ (K.interpret stmt).accept circuit hsat, rfl⟩

#assert_axioms dfa_bound_verify_sound

/-- ⚑ **`dfa_bound_identifies_record_or_collides`** — the form that names THE record (codex round 1,
`docs/automata/codex-synthesis.md` §1): for a named `record` whose commitment is the disclosed `c`,
an accepted proof yields an accepting run that READS `record`, or an accepting run whose word is a
DIFFERENT preimage of the same commitment — the collision event, pinned to the extracted word and
the record. A computational consumer bounds that event by the scheme's binding advantage
(CERTIFICATES.md P1); this theorem does not assume it, it NAMES it. (`dfa_bound_verify_sound` says
"some word commits to `c`", which at a trivial scheme `commit := fun _ => ()` is as weak as the
unbound form; this one is not: the disjunct is a concrete equivocation.) -/
theorem dfa_bound_identifies_record_or_collides {State Sym D Input : Type} {S : ContentScheme Sym D}
    [K : DfaBoundVerifierKernel State Sym D S Proof Input]
    (hext : K.extractable (Input := Input)) (stmt : Input) (proof : Proof)
    (haccept : K.verify stmt proof = true)
    (record : List Sym) (hrec : S.commit record = (K.interpret stmt).c) :
    ∃ trace : List (Step State Sym), DfaAccepts (K.interpret stmt).δ (K.interpret stmt).q₀ (K.interpret stmt).accept trace ∧
      (traceWord trace = record ∨
        (traceWord trace ≠ record ∧ S.commit (traceWord trace) = S.commit record)) := by
  obtain ⟨w, hw, trace, hacc, hword⟩ := dfa_bound_verify_sound (K := K) hext stmt proof haccept
  refine ⟨trace, hacc, ?_⟩
  by_cases heq : traceWord trace = record
  · exact Or.inl heq
  · exact Or.inr ⟨heq, by rw [hword, hw, hrec]⟩

#assert_axioms dfa_bound_identifies_record_or_collides

/-! ## Layer C — the kind obligation + the DIAL wiring at the `fullDisclosure` floor.

The DFA structure and the entire accepted state-trace are PUBLIC — the verifier learns the cleartext
automaton and the whole run. So the epistemic floor is `fullDisclosure` (the top of the dial: cleartext
+ trace), per `PHASE-CRYPTOKERNEL.md §5` ("dial `fullDisclosure`/`selective`"). This is the FIRST kind
to sit at the dial's ceiling — Merkle/NonMembership sit at the ZK floor, Pedersen/Temporal at
`selective`. (Were the trace blinded — a private structural match — the floor would drop to `selective`;
that is the documented variant. Here we wire the public-automaton case.) -/

open Dregg2.Authority.Predicate Dregg2.Laws Metatheory

/-- **`KindObligation`** for DFA — statement algebra `Statement State Sym`, **dial floor =
`fullDisclosure`** (the automaton and the run are public; cleartext + trace, the dial ceiling). -/
structure KindObligation (State Sym : Type) where
  /-- The public-input algebra: the disclosed automaton. -/
  Statement : Type
  /-- The dial floor — `fullDisclosure` for the public DFA. -/
  dialFloor : Dial

/-- The DFA kind's obligation: statement = the disclosed automaton PLUS the content commitment
(`BoundStatement`), floor = `fullDisclosure`. -/
def dfaKindObligation (State Sym D : Type) : KindObligation State Sym where
  Statement := BoundStatement State Sym D
  dialFloor := Dial.fullDisclosure

@[simp] theorem dfaKindObligation_floor (State Sym D : Type) :
    (dfaKindObligation State Sym D).dialFloor = Dial.fullDisclosure := rfl

/-- `fullDisclosure` is strictly above `selective`: the public DFA discloses more than Pedersen's
chosen-facts floor. -/
theorem dfa_floor_above_selective (State Sym D : Type) :
    Dial.selective < (dfaKindObligation State Sym D).dialFloor := by
  show Dial.selective < Dial.fullDisclosure
  exact Dial.selective_lt_fullDisclosure

/-! ### The dial wiring — `DiscloseAt` instantiated at the BOUND DFA verifier's `fullDisclosure` floor.

Re-pointed (2026-11-05) from `DfaVerifierKernel` to `DfaBoundVerifierKernel`: the registry's
`dfa` entry now dispatches on `BoundStatement`, and the cascade's third conjunct is the
content-bound conclusion. -/

section Wiring

variable {S Y D Input : Type} {P : Type}

/-- A `Verifier Input P` from the bound kernel's §8 `verify` oracle. -/
def dfaVerifier (C : ContentScheme Y D) [K : DfaBoundVerifierKernel S Y D C P Input] :
    Verifier Input P :=
  fun stmt proof => K.verify stmt proof

/-- The DFA-kind registry: the bound `verify` oracle installed at `dfa`. -/
def dfaReg (C : ContentScheme Y D) [DfaBoundVerifierKernel S Y D C P Input]
    (base : Registry Input P) : Registry Input P :=
  fun j => if j = .dfa then some (dfaVerifier (S := S) C) else base j

/-- The `Verifiable` seam this kind dispatches through (explicit `base`, not auto-synthesized). -/
@[reducible] def dfaSeam (C : ContentScheme Y D) [DfaBoundVerifierKernel S Y D C P Input]
    (base : Registry Input P) : Verifiable Input P :=
  verifiableOfRegistry (dfaReg (S := S) C base) .dfa

/-- **`dfaDisclose` — the dial pinned to the bound DFA verifier.** `accepts d` is the
position-independent `Discharged stmt proof`; `accepts_eq := fun _ => Iff.rfl`. -/
def dfaDisclose (C : ContentScheme Y D) [DfaBoundVerifierKernel S Y D C P Input]
    (base : Registry Input P) (stmt : Input) (proof : P) :
    @DiscloseAt Unit Input P _ (dfaSeam (S := S) C base) :=
  letI : Verifiable Input P := dfaSeam (S := S) C base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := stmt
    wit := proof
    accepts := fun _ => Discharged stmt proof
    accepts_eq := fun _ => Iff.rfl }

/-- **`dfa_dial_wired`** — the DFA kind's floor is `fullDisclosure` (public automaton + run), the
dial's bottom notch IS the verifier's `Discharged` bit, and an accepting proof proves a valid run
exists THAT READS A WORD COMMITTING TO THE DISCLOSED `c`. Dial pinned to the per-kind verifier. -/
theorem dfa_dial_wired (C : ContentScheme Y D) [K : DfaBoundVerifierKernel S Y D C P Input]
    (hext : K.extractable (Input := Input))
    (base : Registry Input P) (stmt : Input) (proof : P) :
    -- (1) the floor is fullDisclosure:
    (dfaKindObligation S Y D).dialFloor = Dial.fullDisclosure ∧
    -- (2) the dial's bottom notch accepts IFF the DFA verifier discharges:
    (@DiscloseAt.accepts Unit Input P _ (dfaSeam (S := S) C base)
        (dfaDisclose (S := S) C base stmt proof) (⊥ : Dial)
      ↔ @Discharged Input P (dfaSeam (S := S) C base) stmt proof) ∧
    -- (3) and an accepting proof PROVES a valid accepting run over a word committing to `c`:
    (K.verify stmt proof = true →
      ∃ w : List Y, C.commit w = (K.interpret stmt).c ∧
        ∃ trace : List (Step S Y),
          DfaAccepts (K.interpret stmt).δ (K.interpret stmt).q₀ (K.interpret stmt).accept trace ∧ traceWord trace = w) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit Input P _ (dfaSeam (S := S) C base)
      (dfaDisclose (S := S) C base stmt proof)
  · exact fun haccept => dfa_bound_verify_sound (K := K) hext stmt proof haccept

/-- **`dfa_registry_cascade`** — registering the DFA kind, an accepted proof both `Discharged`s the
kind's predicate (`registry_sound`) and — given `extractable` — proves a content-bound accepting run
exists (`dfa_bound_verify_sound`). Single trust boundary: `extractable`. -/
theorem dfa_registry_cascade (C : ContentScheme Y D) [K : DfaBoundVerifierKernel S Y D C P Input]
    (hext : K.extractable (Input := Input))
    (base : Registry Input P)
    (stmt : Input) (proof : P)
    (haccept : K.verify stmt proof = true) :
    (@Discharged Input P (verifiableOfRegistry (dfaReg (S := S) C base) .dfa) stmt proof)
      ∧ ∃ w : List Y, C.commit w = (K.interpret stmt).c ∧
          ∃ trace : List (Step S Y),
            DfaAccepts (K.interpret stmt).δ (K.interpret stmt).q₀ (K.interpret stmt).accept trace ∧ traceWord trace = w := by
  refine ⟨?_, dfa_bound_verify_sound (K := K) hext stmt proof haccept⟩
  apply registry_sound (dfaReg (S := S) C base) .dfa stmt proof
  show registryVerify (dfaReg (S := S) C base) .dfa stmt proof = true
  unfold registryVerify dfaReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

#assert_axioms dfa_dial_wired
#assert_axioms dfa_registry_cascade

/-! ## `Reference` — a concrete kernel + non-vacuity witnesses over `ℕ`/`ℕ`.

A concrete automaton recognizing `a⁺b` (one-or-more `a` then a `b`), in the retired builder's
`dfa_lookup_table` shape: states `{0,1,2,3}`, bytes `{0x61='a', 0x62='b'}`. The transition relation `δ` is the
table's membership predicate; the run for `"aab"` is `0 →a 1 →a 1 →b 2`, ending in the accept state `2`.

`Dregg2.Automata.DfaBoundReference` supplies the executable full-premise bound kernel:
its input is a Boolean transition table and accepting set, interpreted as this semantic statement.
It checks the trace and its record commitment, instantiates the generic theorem below, and rejects
both a nonaccepting word and a valid trace spliced against the wrong record. No decision oracle for
arbitrary propositions is used. The examples here retain the original `a⁺b` relation witnesses. -/

namespace Reference

/-- The transition relation of the `a⁺b` DFA (the retired `dfa_lookup_table` shape): the five table
entries as a `δ` predicate over `ℕ` states / `ℕ` (byte) symbols. Decidable (a disjunction of `ℕ`
equalities). -/
def δ : Nat → Nat → Nat → Prop := fun s b n =>
  (s = 0 ∧ b = 0x61 ∧ n = 1) ∨   -- state 0 + 'a' -> 1
  (s = 1 ∧ b = 0x61 ∧ n = 1) ∨   -- state 1 + 'a' -> 1
  (s = 1 ∧ b = 0x62 ∧ n = 2) ∨   -- state 1 + 'b' -> 2 (accept)
  (s = 2 ∧ b = 0x61 ∧ n = 3) ∨   -- state 2 + 'a' -> 3
  (s = 2 ∧ b = 0x62 ∧ n = 3)     -- state 2 + 'b' -> 3

/-- The initial state. -/
def q₀ : Nat := 0
/-- The accept predicate: state `2` accepts. -/
def accept : Nat → Prop := fun s => s = 2

/-- The accepting run for `"aab"`: `0 →a 1 →a 1 →b 2`. -/
def aabTrace : List (Step Nat Nat) :=
  [ { state := 0, sym := 0x61, next := 1 },
    { state := 1, sym := 0x61, next := 1 },
    { state := 1, sym := 0x62, next := 2 } ]

/-- Non-vacuity of the SOUNDNESS heart: the `"aab"` run is a genuine accepting run (`DfaAccepts`). The
per-step `δ`-validity, chaining, and the initial/accept boundaries all hold concretely. -/
theorem aab_accepts : DfaAccepts δ q₀ accept aabTrace := by
  refine ⟨_, _, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · -- accept (last.next) : last.next = 2, accept 2 = (2 = 2)
    rfl
  · -- every step is δ-valid
    intro s hs
    simp only [aabTrace, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · -- chained: 1 = 1, 1 = 1
    exact ⟨rfl, rfl, trivial⟩

/-- Non-vacuity of the BRIDGE: the `"aab"` accepting run gives a satisfying trace (`dfa_complete`). -/
example : ∃ circuit : CircuitIR Nat Nat, Satisfies δ q₀ accept circuit :=
  dfa_complete δ q₀ accept aabTrace aab_accepts

/-- Non-vacuity of the BRIDGE soundness half, end-to-end on the concrete automaton: the `dfa_bridge`'s
SOUNDNESS conjunct, fed the canonical `"aab"` satisfying trace (which is exactly the genuine accepting
run), certifies `DfaAccepts`. This exercises the deliverable on a real automaton (the `a⁺b` DFA of
`circuit.rs:1724`) with NO crypto. -/
example : DfaAccepts δ q₀ accept aabTrace :=
  (dfa_bridge δ q₀ accept aabTrace).1 ⟨aabTrace⟩ rfl aab_accepts

/-! ### ⚑ THE FALSIFIER — the splice meets the UNBOUND extract shape and refutes the BOUND one.

The acceptance test of a kernel that checks the proof (a trace) against the AUTOMATON ONLY — the
statement's commitment is never read. Under the unbound shape (`DfaVerifierKernel.extract`'s
conclusion) it is a perfectly good carrier: an accepting run is a satisfying trace. Under the bound
shape it is REFUTED: the commitment `[0x7a]` (identity scheme: the word `"z"` itself) is accepted
together with the `"aab"` run, and no satisfying trace reads `"z"` because `δ` has no `0x7a` edge.
This is the separation the repair buys, exhibited rather than asserted. -/

/-- The splice's acceptance test: the proof is a run of the reference automaton; `c` is ignored. -/
def spliceAccepts (_c : List Nat) (tr : List (Step Nat Nat)) : Prop := DfaAccepts δ q₀ accept tr

/-- The same test at an arbitrary commitment type (for the scheme-generic separation). -/
def spliceAccepts' {D : Type} (_c : D) (tr : List (Step Nat Nat)) : Prop := DfaAccepts δ q₀ accept tr

/-- The identity content scheme: the commitment IS the word. -/
def idScheme : ContentScheme Nat (List Nat) := ⟨id⟩

/-- **The splice MEETS the unbound extract shape**: whatever `c` says, an accepted run is a
satisfying trace. (This is why the unbound statement certifies "any record".) -/
theorem splice_meets_unbound :
    ∀ (c : List Nat) (tr : List (Step Nat Nat)), spliceAccepts c tr →
      ∃ circuit : CircuitIR Nat Nat, Satisfies δ q₀ accept circuit :=
  fun _ tr h => ⟨⟨tr⟩, h⟩

/-- **The splice FAILS the bound extract shape**: at `c := [0x7a]` and the `"aab"` run it accepts,
yet no satisfying trace reads a word committing to `[0x7a]`. -/
theorem splice_fails_bound :
    ¬ ∀ (c : List Nat) (tr : List (Step Nat Nat)), spliceAccepts c tr →
      ∃ circuit : CircuitIR Nat Nat,
        Satisfies δ q₀ accept circuit ∧ idScheme.commit (traceWord circuit.trace) = c := by
  intro hall
  obtain ⟨circuit, hsat, hw⟩ := hall [0x7a] aabTrace aab_accepts
  obtain ⟨_, _, _, _, _, _, hvalid, _⟩ := hsat
  have hw' : traceWord circuit.trace = [0x7a] := hw
  cases htr : circuit.trace with
  | nil => rw [htr] at hw'; simp at hw'
  | cons s rest =>
    rw [htr] at hw'
    simp only [traceWord_cons, List.cons.injEq] at hw'
    have hs : s.sym = 0x7a := hw'.1
    have hv := hvalid s (by rw [htr]; exact List.mem_cons_self)
    unfold stepValid δ at hv
    rw [hs] at hv
    rcases hv with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega

/-- **The separation, scheme-generic** (codex round 1 §2): for ANY scheme `S` and commitment `c` that
NO accepting run's word opens, the splice accepts `(c, aabTrace)` and the bound extract shape is
refuted at `c`. The identity scheme discharges the hypothesis at `c := [0x7a]` (`splice_fails_bound`
is this theorem's instance); a constant scheme cannot, which is exactly why a constant scheme makes
the bound statement as weak as the unbound one. -/
theorem splice_fails_bound_of_sep {D : Type} (S : ContentScheme Nat D) (c : D)
    (hsep : ∀ tr : List (Step Nat Nat), DfaAccepts δ q₀ accept tr → S.commit (traceWord tr) ≠ c) :
    spliceAccepts' c aabTrace ∧
      ¬ ∃ circuit : CircuitIR Nat Nat,
        Satisfies δ q₀ accept circuit ∧ S.commit (traceWord circuit.trace) = c := by
  refine ⟨aab_accepts, ?_⟩
  rintro ⟨circuit, hsat, hc⟩
  exact hsep circuit.trace (dfa_sound δ q₀ accept circuit hsat) hc

#assert_axioms splice_meets_unbound
#assert_axioms splice_fails_bound
#assert_axioms splice_fails_bound_of_sep

/-! ### Executable reference instance

The generic bound kernel separates executable input presentation from its `BoundStatement`
interpretation. `Automata/DfaBoundReference.lean` instantiates it using Boolean automaton data and
an identity word commitment. Its accepted/extractable witness exercises
`dfa_bound_identifies_record_or_collides`; rejecting-word and wrong-record counterexamples show
that the checker neither accepts all traces nor ignores the record. This is a proved reference
checker, not a STARK extraction theorem or a hiding commitment. -/

end Reference

end Dregg2.Crypto.Dfa
