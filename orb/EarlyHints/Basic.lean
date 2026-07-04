/-!
# HTTP 103 Early Hints (RFC 8297)

A response may emit zero or more `103` informational responses (each carrying
preload `Link` headers) before exactly one final (non-1xx) response. The model
is a two-state builder: while `building`, informational responses accumulate;
`emitFinal` commits the one final response and moves to `committed`, after
which nothing further is emitted.

The theorems: every informational response precedes the final (an ordering
invariant on the emitted sequence); at most one final is emitted; and an
informational response does not commit the final status.
-/

namespace EarlyHints

/-- An informational (`103`) response: preload hint headers, never a body. -/
structure Info where
  headers : List (String × String)
deriving Repr, DecidableEq

/-- The one final (non-1xx) response. -/
structure Final where
  status : Nat
  headers : List (String × String)
  body : List UInt8
deriving Repr, DecidableEq

/-- An emitted message: an informational hint or the final response. -/
inductive Msg where
  | info (r : Info)
  | final (r : Final)
deriving Repr, DecidableEq

/-- Is this an informational hint? -/
def Msg.isInfo : Msg → Bool
  | .info _ => true
  | .final _ => false

/-- Builder state: still accumulating hints, or the final has been committed. -/
inductive State where
  | building
  | committed
deriving Repr, DecidableEq

/-- Actions the response builder accepts. -/
inductive Action where
  | emitInfo (r : Info)
  | emitFinal (r : Final)

/-- One step: emit a hint (only while building), commit the final (building →
committed), or — once committed — reject (emit nothing). -/
def step : State → Action → State × Option Msg
  | .building, .emitInfo r => (.building, some (.info r))
  | .building, .emitFinal r => (.committed, some (.final r))
  | .committed, _ => (.committed, none)

/-- Run a sequence of actions, collecting the emitted messages in order. -/
def run (st : State) : List Action → State × List Msg
  | [] => (st, [])
  | a :: rest =>
    let (st₁, m) := step st a
    let (st₂, ms) := run st₁ rest
    (st₂, m.toList ++ ms)

/-- Every message in a list is an informational hint. -/
def allInfo (ms : List Msg) : Prop := ms.all Msg.isInfo = true

/-- Once committed, the builder emits nothing further, for any action tail. -/
theorem run_committed_nil (acts : List Action) :
    run .committed acts = (.committed, []) := by
  induction acts with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [run, step, ih]

/-- `run` on a hint step: prepend the hint, keep the recursive state. -/
theorem run_info_cons (r : Info) (rest : List Action) :
    run .building (.emitInfo r :: rest)
      = ((run .building rest).1, Msg.info r :: (run .building rest).2) := by
  simp [run, step]

/-- `run` on a final step: commit, emit exactly the final, then nothing. -/
theorem run_final_cons (r : Final) (rest : List Action) :
    run .building (.emitFinal r :: rest) = (.committed, [Msg.final r]) := by
  simp [run, step, run_committed_nil]

/-- Filtering the non-informational messages out of an all-informational list
leaves nothing. -/
theorem filter_nonInfo_allInfo (ms : List Msg) (h : allInfo ms) :
    ms.filter (fun m => !m.isInfo) = [] := by
  induction ms with
  | nil => rfl
  | cons x xs ih =>
    simp only [allInfo, List.all_cons, Bool.and_eq_true] at h
    have hx : (!x.isInfo) = false := by simp [h.1]
    simp only [List.filter_cons, hx, if_false]
    exact ih (by simp [allInfo, h.2])

/-- **Shape theorem.** Running from `building`, the emitted sequence is either
all informational hints (never finalized) or a run of hints followed by exactly
one final (finalized). In particular no hint is ever emitted after the final. -/
theorem run_building_shape (acts : List Action) :
    ((run .building acts).1 = .building ∧ allInfo (run .building acts).2) ∨
    ((run .building acts).1 = .committed ∧
      ∃ pre f, (run .building acts).2 = pre ++ [Msg.final f] ∧ allInfo pre) := by
  induction acts with
  | nil => exact Or.inl ⟨rfl, by simp [allInfo, run]⟩
  | cons a rest ih =>
    cases a with
    | emitInfo r =>
      rw [run_info_cons]
      rcases ih with ⟨hst, hall⟩ | ⟨hst, pre, f, heq, hpre⟩
      · refine Or.inl ⟨hst, ?_⟩
        simp only [allInfo, List.all_cons, Msg.isInfo, Bool.true_and]
        simpa [allInfo] using hall
      · refine Or.inr ⟨hst, Msg.info r :: pre, f, ?_, ?_⟩
        · simp only [heq, List.cons_append]
        · simp only [allInfo, List.all_cons, Msg.isInfo, Bool.true_and]
          simpa [allInfo] using hpre
    | emitFinal r =>
      rw [run_final_cons]
      exact Or.inr ⟨rfl, [], r, by simp, by simp [allInfo]⟩

/-- **At most one final.** No response emits two final responses. -/
theorem at_most_one_final (acts : List Action) :
    ((run .building acts).2.filter (fun m => !m.isInfo)).length ≤ 1 := by
  rcases run_building_shape acts with ⟨_, hall⟩ | ⟨_, pre, f, heq, hpre⟩
  · rw [filter_nonInfo_allInfo _ hall]; simp
  · rw [heq, List.filter_append, filter_nonInfo_allInfo _ hpre]
    simp [Msg.isInfo]

/-- Emitting a hint while building stays in `building` (the final is not yet
chosen). -/
theorem emitInfo_building (r : Info) :
    step .building (.emitInfo r) = (.building, some (.info r)) := rfl

/-- Committing the final moves to `committed` and emits the final. -/
theorem emitFinal_commits (r : Final) :
    step .building (.emitFinal r) = (.committed, some (.final r)) := rfl

/-- After commit, no action emits anything. -/
theorem committed_emits_nothing (a : Action) :
    (step .committed a).2 = none := by cases a <;> rfl

def version : String := "0.1.0"

end EarlyHints
