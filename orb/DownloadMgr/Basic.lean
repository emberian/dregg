/-
# Download / session manager — core datatypes and the job step function

A `Job` tracks the lifecycle of a single file download. Its lifecycle is a
five-state machine

    queued → active → (paused | complete | failed)

with `complete` and `failed` terminal (absorbing). Alongside the state the job
carries three counters:

* `recv`     — the received-byte cursor: the length of the contiguous prefix of
               the resource obtained so far. This is the offset a `Range`
               resume requests from.
* `attempts` — retryable failures consumed so far.
* `budget`   — the retry budget `N`: the maximum number of retryable failures
               the job may absorb before it terminates as `failed`.

`step : Job → Event → Job × List Output` is a total function (every state/event
pair has exactly one result), hence deterministic by construction. Impossible
events in a given state are absorbed as no-ops so the machine is total without
partial cases. The `Output` list records what a step would put on the wire or
hand to the sink; the only wire-relevant output for resume is `reqFrom start`,
a `Range: bytes=start-` request for the open-ended suffix from `start`.
-/

namespace DownloadMgr

/-- Lifecycle state of a download job. -/
inductive JobState where
  | queued
  | active
  | paused
  | complete
  | failed
deriving DecidableEq, Repr

/-- A single download job. `recv` is the received-byte cursor (contiguous prefix
length); `attempts` is retries consumed; `budget` is the retry budget `N`. -/
structure Job where
  st : JobState
  recv : Nat
  attempts : Nat
  budget : Nat
deriving Repr

/-- A fresh job with retry budget `budget`: queued, cursor at 0, no attempts. -/
def Job.init (budget : Nat) : Job :=
  { st := .queued, recv := 0, attempts := 0, budget := budget }

/-- Events driving the machine. -/
inductive Event where
  /-- Start (from `queued`) or resume (from `paused`): issue the request. -/
  | activate
  /-- While active, receive `k` more contiguous bytes. -/
  | deliver (k : Nat)
  /-- While active, pause: the cursor is recorded for a later resume. -/
  | pause
  /-- While active, the transfer completed. -/
  | finish
  /-- While active, a retryable (transient) failure. -/
  | failSoft
  /-- While active, a non-retryable (fatal) failure — terminates immediately. -/
  | failHard
deriving DecidableEq, Repr

/-- What a step puts on the wire / hands to the sink. -/
inductive Output where
  /-- A request for the open-ended suffix `Range: bytes=start-`
      (`start = 0` is a plain full GET). -/
  | reqFrom (start : Nat)
  /-- `k` bytes handed to the sink. -/
  | got (k : Nat)
  /-- The transfer completed. -/
  | completed
  /-- The transfer was aborted (fatal, or retry budget exhausted). -/
  | aborted
deriving DecidableEq, Repr

/-- A job in a terminal state. -/
def Job.terminal (j : Job) : Bool :=
  match j.st with
  | .complete => true
  | .failed => true
  | _ => false

/-- The job step function. Total (every `(state, event)` pair is covered) and
therefore deterministic. `complete`/`failed` absorb every event. On `activate`
the machine emits `reqFrom recv` — a `Range` request for exactly the suffix past
the recorded cursor. A retryable failure requeues the job (consuming one unit of
budget) only while `attempts < budget`; once the budget is spent it terminates
as `failed`. A fatal failure terminates immediately, without consuming budget. -/
def step (j : Job) (e : Event) : Job × List Output :=
  match j.st, e with
  | .complete, _ => (j, [])
  | .failed, _ => (j, [])
  | .queued, .activate => ({ j with st := .active }, [Output.reqFrom j.recv])
  | .queued, _ => (j, [])
  | .paused, .activate => ({ j with st := .active }, [Output.reqFrom j.recv])
  | .paused, _ => (j, [])
  | .active, .deliver k => ({ j with recv := j.recv + k }, [Output.got k])
  | .active, .pause => ({ j with st := .paused }, [])
  | .active, .finish => ({ j with st := .complete }, [Output.completed])
  | .active, .failHard => ({ j with st := .failed }, [Output.aborted])
  | .active, .failSoft =>
      if j.attempts < j.budget then
        ({ j with st := .queued, attempts := j.attempts + 1 }, [])
      else
        ({ j with st := .failed }, [Output.aborted])
  | .active, .activate => (j, [])

/-- Run the machine over a list of events, concatenating outputs left to right. -/
def run (j : Job) : List Event → Job × List Output
  | [] => (j, [])
  | e :: es =>
    let r₁ := step j e
    let r₂ := run r₁.1 es
    (r₂.1, r₁.2 ++ r₂.2)

end DownloadMgr
