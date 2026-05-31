/-
# Dregg2.Crypto.Dfa — the FIFTH end-to-end §8 discharge: DFA structural-match acceptance.

**The next obligation after Merkle / Pedersen / NonMembership / Temporal
(`docs/rebuild/PHASE-CRYPTOKERNEL.md §5` "Path to the rest": Temporal/Dfa "need `Lookup`/`Gated` in
`CircuitIR`; dial `fullDisclosure`/`selective`").** This discharges DFA acceptance
(`WitnessedPredicateKind::Dfa`): a trace of automaton states, threaded by a transition relation `δ`,
starts in the initial state and ends in an accepting state — i.e. the input string is accepted by the
deterministic automaton. This is the `dfa_lookup_descriptor` family (`circuit/src/dsl/circuit.rs:1746`):
the trace is rows `[state, byte, next_state]`, a `Lookup` constraint asserts each
`(state, byte, next_state)` is a member of the transition table (`dfa_lookup_table`,
`circuit.rs:1724`), a `Transition` constraint chains `next_state` to the following row's `state`, and
boundary `PiBinding`s pin the first state to the initial state and the last to acceptance.

The cascade mirrors the prior kinds:

    dfa_bridge       : Satisfies dfaCircuit (q₀, accept, trace) ↔ DfaAccepts δ q₀ accept trace
      [the gadget, FULLY proven — per-step `Lookup` membership + initial/accept boundary, no seam]
    dfa_verify_sound : verify accepts → DfaAccepts …
      [DERIVED off the bridge, given the STARK `extractable` carrier]
    dfa_dial_wired   : the dial pinned to the verifier at the `fullDisclosure` floor
      [the DFA structure and the accepted state-trace are PUBLIC ⇒ `fullDisclosure`]

**The per-step transition validity + initial/accept boundary is the genuinely-grounded part** (and
the heart of the bridge): a satisfying trace is precisely a valid run of the automaton — every step's
`(state, byte, next)` lies in the transition relation (the `Lookup` membership, modeled as a `δ`
predicate exactly as the table lookup abstracts), the steps chain, and the endpoints are initial /
accepting. This is FULLY proved combinatorics on the trace list; there is NO `compress`/hash in the
DFA gadget, so NO primitive seam at all. The ONLY cryptographic residue is the STARK `extractable`
carrier (a `Prop`, passed as a hypothesis), binding the disclosed statement to a satisfying trace.

**Dial = `fullDisclosure`** (per `PHASE-CRYPTOKERNEL.md §5`): the DFA structure and the entire
state-trace are public — the verifier learns cleartext + the whole run, the top of the dial.
-/
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
`Lookup` transition table (`dfa_lookup_table`, `circuit.rs:1724` — the table's entries ARE the `δ`
graph). A run is a list of steps; it ACCEPTS iff each step is a valid `δ` transition, consecutive
steps chain (`next` of one is `state` of the following), the first `state` is the initial state `q₀`,
and the final `next` is accepting (`accept : State → Prop`). This is exactly the `Lookup` + `Transition`
+ boundary `PiBinding`s the AIR enforces. -/

variable {State Sym : Type u}

/-- A single DFA step: the current `state`, the input `sym`bol read, and the `next` state. Mirrors a
trace row `[state, byte, next_state]` (`dfa_lookup_descriptor`, `circuit.rs:1746`). -/
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
`state`. Stated over the step list. -/
def chained : List (Step State Sym) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b.state = a.next ∧ chained (b :: rest)

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

Mirrors `dfa_lookup_descriptor` (`circuit.rs:1746`): the trace is the row list, each row a `Step`. The
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
is the conjunction `dfa_lookup_descriptor` enforces — IDENTICAL in shape to `DfaAccepts` (the IR and
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

/-- **`dfa_bridge` — THE deliverable (the analog of `merkle_bridge`).** The DFA AIR's satisfiability is
EXACTLY a valid accepting run of the automaton:

  * `→` (SOUNDNESS): a satisfying trace's per-step `Lookup` validity + chaining + boundaries ARE a
    valid accepting run (`dfa_sound`).
  * `←` (COMPLETENESS): a genuine accepting run gives a satisfying trace (`dfa_complete`).

The DFA gadget is pure structural matching — the `Lookup` table is abstracted as the transition
relation `δ` (its membership predicate, exactly what the lookup constraint enforces), `compress` does
NOT appear, so there is NO primitive seam ANYWHERE. The ONLY cryptographic residue is the STARK
`extractable` carrier (consumed by `dfa_verify_sound`), binding the disclosed statement to a
satisfying trace. Stated over `circuit.trace` on the `→` side (the witnessed run) and existentially on
the `←` side (the prover's run is the witness). -/
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

-- TRIPWIRES: the DFA gadget is FULLY proven with NO primitive seam — both bridge directions are
-- kernel-clean. The `Lookup` is abstracted as the transition relation `δ`; there is no hash/`compress`
-- to flag (the DFA predicate is pure structural matching).
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
  exists. A `Prop`; never proved, never `sorry`. -/
  extractable : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying DFA trace for the disclosed
  automaton. The named form the bridge composes with — STARK soundness. -/
  extract : extractable →
    ∀ (stmt : Statement State Sym) (proof : Proof), verify stmt proof = true →
      ∃ circuit : CircuitIR State Sym, Satisfies stmt.δ stmt.q₀ stmt.accept circuit

variable {Proof : Type}

/-- **`dfa_verify_sound` — the DERIVED verify law (the analog of `merkle_verify_sound`).** Given the
STARK-soundness carrier `extractable`, an accepted DFA proof PROVES a valid accepting run of the
disclosed automaton exists:

    verify stmt proof = true  →  ∃ trace, DfaAccepts stmt.δ stmt.q₀ stmt.accept trace

The proof composes `extract` (accept ⇒ satisfying trace, the crypto carrier) with `dfa_bridge`'s
SOUNDNESS half (satisfying trace ⇒ accepting run, FULLY proved). The verify law is DERIVED, not
assumed; the only hypothesis is `extractable`. -/
theorem dfa_verify_sound {State Sym : Type} [K : DfaVerifierKernel State Sym Proof]
    (hext : K.extractable) (stmt : Statement State Sym) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ trace : List (Step State Sym), DfaAccepts stmt.δ stmt.q₀ stmt.accept trace := by
  obtain ⟨circuit, hsat⟩ := K.extract hext stmt proof haccept
  exact ⟨circuit.trace, dfa_sound stmt.δ stmt.q₀ stmt.accept circuit hsat⟩

#assert_axioms dfa_verify_sound

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

/-- The DFA kind's obligation: statement = the disclosed automaton, floor = `fullDisclosure`. -/
def dfaKindObligation (State Sym : Type) : KindObligation State Sym where
  Statement := Statement State Sym
  dialFloor := Dial.fullDisclosure

@[simp] theorem dfaKindObligation_floor (State Sym : Type) :
    (dfaKindObligation State Sym).dialFloor = Dial.fullDisclosure := rfl

/-- `fullDisclosure` is strictly above `selective` (the public DFA discloses MORE than Pedersen's
chosen-facts floor): the floor is at the dial ceiling, non-degenerate above `selective`. -/
theorem dfa_floor_above_selective (State Sym : Type) :
    Dial.selective < (dfaKindObligation State Sym).dialFloor := by
  show Dial.selective < Dial.fullDisclosure
  exact Dial.selective_lt_fullDisclosure

/-! ### The dial wiring — `DiscloseAt` instantiated at the DFA verifier's `fullDisclosure` floor. -/

section Wiring

variable {S Y : Type} {P : Type}

/-- A `Verifier (Statement S Y) P` from the kernel's §8 `verify` oracle. -/
def dfaVerifier [K : DfaVerifierKernel S Y P] : Verifier (Statement S Y) P :=
  fun stmt proof => K.verify stmt proof

/-- The DFA-kind registry: the §8 `verify` oracle installed at `dfa`. -/
def dfaReg [DfaVerifierKernel S Y P]
    (base : Registry (Statement S Y) P) : Registry (Statement S Y) P :=
  fun j => if j = .dfa then some dfaVerifier else base j

/-- The `Verifiable` seam this kind dispatches through (explicit `base`, not auto-synthesized). -/
@[reducible] def dfaSeam [DfaVerifierKernel S Y P]
    (base : Registry (Statement S Y) P) : Verifiable (Statement S Y) P :=
  verifiableOfRegistry (dfaReg base) .dfa

/-- **`dfaDisclose` — the dial pinned to the DFA verifier.** `accepts d` is the position-independent
`Discharged stmt proof`; `accepts_eq := fun _ => Iff.rfl`. Realizes "instantiate `DiscloseAt` at the
`fullDisclosure` floor (the automaton and run are public)". -/
def dfaDisclose [DfaVerifierKernel S Y P]
    (base : Registry (Statement S Y) P) (stmt : Statement S Y) (proof : P) :
    @DiscloseAt Unit (Statement S Y) P _ (dfaSeam base) :=
  letI : Verifiable (Statement S Y) P := dfaSeam base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := stmt
    wit := proof
    accepts := fun _ => Discharged stmt proof
    accepts_eq := fun _ => Iff.rfl }

/-- **`dfa_dial_wired` — THE DIAL WIRING (the analog of `merkle_dial_wired`).** The DFA kind's
epistemic floor is `fullDisclosure` (the public automaton + run), the dial's bottom notch's acceptance
bit IS the DFA verifier's `Discharged` bit, and — given STARK `extractable` — an accepting proof PROVES
a valid accepting run exists. The dial is pinned to the per-kind verifier. -/
theorem dfa_dial_wired [K : DfaVerifierKernel S Y P]
    (hext : K.extractable)
    (base : Registry (Statement S Y) P) (stmt : Statement S Y) (proof : P) :
    -- (1) the floor is fullDisclosure:
    (dfaKindObligation S Y).dialFloor = Dial.fullDisclosure ∧
    -- (2) the dial's bottom notch accepts IFF the DFA verifier discharges:
    (@DiscloseAt.accepts Unit (Statement S Y) P _ (dfaSeam base)
        (dfaDisclose base stmt proof) (⊥ : Dial)
      ↔ @Discharged (Statement S Y) P (dfaSeam base) stmt proof) ∧
    -- (3) and an accepting proof PROVES a valid accepting run (the cascade):
    (K.verify stmt proof = true →
      ∃ trace : List (Step S Y), DfaAccepts stmt.δ stmt.q₀ stmt.accept trace) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit (Statement S Y) P _ (dfaSeam base)
      (dfaDisclose base stmt proof)
  · exact fun haccept => dfa_verify_sound hext stmt proof haccept

/-- **`dfa_registry_cascade` — the §8 discharge through the registry (the analog of
`merkle_registry_cascade`).** Registering the DFA kind, an accepted proof both `Discharged`s the kind's
predicate (the registry keystone, `registry_sound`) AND — given the STARK `extractable` carrier —
PROVES a valid accepting run exists (`dfa_verify_sound`). The cascade
`registry_sound ∘ dfa_verify_sound`; the single trust boundary is `extractable`. -/
theorem dfa_registry_cascade [K : DfaVerifierKernel S Y P]
    (hext : K.extractable)
    (base : Registry (Statement S Y) P)
    (stmt : Statement S Y) (proof : P)
    (haccept : K.verify stmt proof = true) :
    (@Discharged (Statement S Y) P (verifiableOfRegistry (dfaReg base) .dfa) stmt proof)
      ∧ ∃ trace : List (Step S Y), DfaAccepts stmt.δ stmt.q₀ stmt.accept trace := by
  refine ⟨?_, dfa_verify_sound hext stmt proof haccept⟩
  apply registry_sound (dfaReg base) .dfa stmt proof
  show registryVerify (dfaReg base) .dfa stmt proof = true
  unfold registryVerify dfaReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

#assert_axioms dfa_dial_wired
#assert_axioms dfa_registry_cascade

/-! ## `Reference` — a concrete kernel + non-vacuity witnesses over `ℕ`/`ℕ`.

A concrete automaton recognizing `a⁺b` (one-or-more `a` then a `b`), the `dfa_lookup_table` of
`circuit.rs:1724`: states `{0,1,2,3}`, bytes `{0x61='a', 0x62='b'}`. The transition relation `δ` is the
table's membership predicate; the run for `"aab"` is `0 →a 1 →a 1 →b 2`, ending in the accept state `2`.

To build an HONEST reference kernel (`verify` genuinely checks the proof against the statement, NO
`sorry`), we use a `Statement` whose `δ`/`accept` are DECIDABLE — they are disjunctions / equalities
over `ℕ`. The `Proof` IS the candidate trace; `verify stmt tr` literally DECIDES whether `tr` is an
accepting run of `stmt`'s automaton (so it works for ANY statement, not just the reference), and
`extract` reads back the decided acceptance. This is the genuine soundness-by-decision; the
`extractable` carrier is `True` because, for this toy, acceptance is decidable in Lean (the real STARK
carrier is what makes it opaque in production). NOT real crypto. -/

namespace Reference

/-- The transition relation of the `a⁺b` DFA (`dfa_lookup_table`, `circuit.rs:1724`): the five table
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
`circuit.rs:1724`) with NO `sorry`, NO crypto. -/
example : DfaAccepts δ q₀ accept aabTrace :=
  (dfa_bridge δ q₀ accept aabTrace).1 ⟨aabTrace⟩ rfl aab_accepts

/-! ### The reference `VerifierKernel`/cascade — an HONEST follow-up.

The cascade (`dfa_verify_sound`/`dfa_registry_cascade`/`dfa_dial_wired`) is proven GENERICALLY above
for any `DfaVerifierKernel` — all kernel-clean. A concrete reference `def`-kernel (the analog of
`Merkle.Reference.refKernel`) would witness it end-to-end over `ℕ`/`ℕ`. The honest obstacle: the
generic `Statement.δ`/`Statement.accept` are `Prop`-VALUED functions, so a toy `verify` cannot DECIDE
acceptance against an ARBITRARY disclosed statement (no `Decidable (DfaAccepts stmt.δ …)` for opaque
`Prop` δ), and `DfaVerifierKernel.extract` is universally quantified over statements. A faithful
reference therefore needs the statement's transition/accept carried as DECIDABLE data (a `Bool`-valued
table + accept set), with `verify` deciding the proof-trace against THAT — a small refactor of the
reference `Statement` (NOT the generic kernel, which is correct as-is). This is left as a documented
`-- OPEN:` honest follow-up; the bridge + the generic verify-sound/cascade/dial are the landed
deliverables, and the bridge non-vacuity above is fully exercised on the real `a⁺b` automaton.

-- OPEN: reference `DfaVerifierKernel` over a decidable-table `Statement` (the `Merkle.Reference`
-- analog). Needs `Statement.δ`/`accept` as `Bool`-valued decidable data so the toy `verify` can
-- DECIDE acceptance against any statement (the generic cascade is already proven & kernel-clean). -/

end Reference

end Dregg2.Crypto.Dfa
