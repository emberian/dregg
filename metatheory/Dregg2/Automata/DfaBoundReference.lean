/-
# An executable full-premise instance of the content-bound DFA kernel.

The input carries a Boolean transition table and accepting set, interpreted as the generic
Prop-valued statement. The checker reads the table, the candidate trace and the identity commitment;
it needs no classical decision oracle. This is a public-trace reference, not a cryptographic prover.
-/
import Dregg2.Crypto.Dfa

namespace Dregg2.Automata.DfaBoundReference

open Dregg2.Crypto.Dfa

structure Input where
  transition : Bool → Bool → Bool → Bool
  start : Bool
  accepting : Bool → Bool
  record : List Bool

/-- Identity commitments expose the whole word and are injective without a hash assumption. -/
def scheme : ContentScheme Bool (List Bool) := ⟨id⟩

def interpret (input : Input) : BoundStatement Bool Bool (List Bool) :=
  { δ := fun s b n => input.transition s b n = true
    q₀ := input.start
    accept := fun s => input.accepting s = true
    c := input.record }

def chainedB : List (Step Bool Bool) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (b.state == a.next) && chainedB (b :: rest)

theorem chainedB_iff (trace : List (Step Bool Bool)) : chainedB trace = true ↔ chained trace := by
  induction trace with
  | nil => simp [chainedB, chained, Dregg2.Crypto.Hypergraph.chain]
  | cons a tail ih =>
    cases tail with
    | nil => simp [chainedB, chained, Dregg2.Crypto.Hypergraph.chain]
    | cons b rest =>
      simp only [chainedB, Bool.and_eq_true, beq_iff_eq, chained, Dregg2.Crypto.Hypergraph.chain]
      exact and_congr_right fun _ => ih

def acceptsB (input : Input) (trace : List (Step Bool Bool)) : Bool :=
  match trace.head?, trace.getLast? with
  | some first, some last =>
      (first.state == input.start) && input.accepting last.next &&
      trace.all (fun s => input.transition s.state s.sym s.next) && chainedB trace
  | _, _ => false

theorem acceptsB_iff (input : Input) (trace : List (Step Bool Bool)) :
    acceptsB input trace = true ↔
      DfaAccepts (interpret input).δ (interpret input).q₀ (interpret input).accept trace := by
  unfold acceptsB DfaAccepts
  cases hh : trace.head? <;> cases hl : trace.getLast? <;>
    simp [interpret, stepValid, chainedB_iff, List.all_eq_true, and_assoc]

def verify (input : Input) (trace : List (Step Bool Bool)) : Bool :=
  acceptsB input trace && (traceWord trace == input.record)

theorem verify_iff (input : Input) (trace : List (Step Bool Bool)) :
    verify input trace = true ↔
      DfaAccepts (interpret input).δ (interpret input).q₀ (interpret input).accept trace ∧
      traceWord trace = input.record := by
  simp [verify, acceptsB_iff]

/-- The state remembers the last symbol; exactly nonempty words ending in true are accepted. -/
def endsTrue (record : List Bool) : Input :=
  ⟨fun _ symbol next => next == symbol, false, id, record⟩

def honest : List (Step Bool Bool) := [⟨false, false, false⟩, ⟨false, true, true⟩]
def rejected : List (Step Bool Bool) := [⟨false, true, true⟩, ⟨true, false, false⟩]

theorem honest_accepts : verify (endsTrue [false, true]) honest = true := by decide

theorem rejecting_word : verify (endsTrue [true, false]) rejected = false := by decide

/-- Only the record binding is removed in the weak check; the same accepting trace is spliced
against a word ending false. The strong checker refuses that exact input/trace pair. -/
theorem wrong_record_separation :
    acceptsB (endsTrue [true, false]) honest = true ∧
    verify (endsTrue [true, false]) honest = false := by decide

/-- The rejected word really is outside the language; choosing a different trace cannot rescue it. -/
theorem rejecting_word_not_in_language :
    ¬ ∃ trace, DfaAccepts (interpret (endsTrue [true, false])).δ false
      (interpret (endsTrue [true, false])).accept trace ∧ traceWord trace = [true, false] := by
  rintro ⟨trace, ⟨first, last, _, hl, _, ha, hv, _⟩, hword⟩
  have hstep := hv last (List.mem_of_getLast? hl)
  have hlast := congrArg List.getLast? hword
  simp only [traceWord, List.getLast?_map, hl, Option.map_some] at hlast
  have hsym : last.sym = false := Option.some.inj hlast
  have hn : last.next = last.sym := by simpa [stepValid, interpret, endsTrue] using hstep
  simp [interpret, endsTrue, hn, hsym] at ha

/-- The reference verifier extracts its actual checked trace. Its carrier is proved, not assumed. -/
instance kernel : DfaBoundVerifierKernel Bool Bool (List Bool) scheme (List (Step Bool Bool)) Input where
  interpret := interpret
  verify := verify
  extractable := True
  extract := by
    intro _ input trace h
    obtain ⟨hacc, hw⟩ := (verify_iff input trace).mp h
    exact ⟨⟨trace⟩, hacc, hw⟩

theorem honest_full_premises :
    kernel.extractable (Input := Input) ∧ kernel.verify (endsTrue [false, true]) honest = true ∧
      scheme.commit [false, true] = (kernel.interpret (endsTrue [false, true])).c :=
  ⟨True.intro, honest_accepts, rfl⟩

/-- The generic bound-kernel theorem fires on a two-symbol alphabet. Identity commitment makes
the named collision branch impossible, so the conclusion is about this exact record. -/
theorem generic_bound_theorem_fires :
    ∃ trace, DfaAccepts (interpret (endsTrue [false, true])).δ false
      (interpret (endsTrue [false, true])).accept trace ∧ traceWord trace = [false, true] := by
  obtain ⟨trace, hacc, hw | hc⟩ := dfa_bound_identifies_record_or_collides
    (K := kernel) honest_full_premises.1 (endsTrue [false, true]) honest
    honest_full_premises.2.1 [false, true] honest_full_premises.2.2
  · exact ⟨trace, hacc, hw⟩
  · exact False.elim (hc.1 hc.2)

/-- info: 'Dregg2.Automata.DfaBoundReference.chainedB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms chainedB_iff
/-- info: 'Dregg2.Automata.DfaBoundReference.acceptsB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms acceptsB_iff
/-- info: 'Dregg2.Automata.DfaBoundReference.verify_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verify_iff
/-- info: 'Dregg2.Automata.DfaBoundReference.honest_accepts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms honest_accepts
/-- info: 'Dregg2.Automata.DfaBoundReference.rejecting_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms rejecting_word
/-- info: 'Dregg2.Automata.DfaBoundReference.wrong_record_separation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrong_record_separation
/-- info: 'Dregg2.Automata.DfaBoundReference.rejecting_word_not_in_language' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rejecting_word_not_in_language
/-- info: 'Dregg2.Automata.DfaBoundReference.honest_full_premises' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms honest_full_premises
/-- info: 'Dregg2.Automata.DfaBoundReference.generic_bound_theorem_fires' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms generic_bound_theorem_fires

end Dregg2.Automata.DfaBoundReference
