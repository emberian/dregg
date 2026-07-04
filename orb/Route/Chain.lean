/-
Route.Chain — the per-route filter (middleware) chain.

A route carries an ordered list of filters applied before its handler. Each
filter is a pure step over the request that returns a `Decision`: `allow` (pass
to the next filter) or `deny` (short-circuit — the handler is NOT reached). A
filter may also transform the request (the `Req` component of its result).

`runChain` folds the filters left to right, recording a TRACE of the filter ids
that actually executed, and stops at the first `deny`. The handler is reached
iff every filter allowed.

The headline is a chain-completeness accounting identity over the step trace:

  * `runChain_reached_trace` — any request that reaches the handler has passed
    each configured filter of its route EXACTLY ONCE, IN ORDER: the executed
    trace equals the configured id list `fs.map Filter.fid` (no skip, no
    reorder, no double).
  * `runChain_reached_nodup` — with distinct configured ids, the executed trace
    is duplicate-free (the "no doubled filter" half, made explicit).
  * `runChain_no_skip` — every configured filter's id appears in the trace when
    the handler is reached.
  * `runChain_trace_prefix` — in EVERY outcome (allow or deny) the executed
    trace is a prefix of the configured id list: the chain never runs an
    unconfigured filter, never reorders, and on deny simply stops early.
-/

namespace Route.Chain

/-- A filter's verdict. `deny` carries a reason and short-circuits the chain. -/
inductive Decision where
  | allow
  | deny (reason : String)
deriving Repr

/-- One filter: a stable id plus a pure step that may transform the request and
returns a verdict. `Req` is the request representation (kept abstract). -/
structure Filter (Req : Type) where
  fid : Nat
  run : Req → Req × Decision

variable {Req : Type}

/-- Fold the chain, threading the (possibly transformed) request and appending
each executed filter's id to the trace `tr`. Stops at the first `deny`.
Result: `(trace, finalRequest, reachedHandler?)`. -/
def stepChain : List (Filter Req) → Req → List Nat → List Nat × Req × Bool
  | [], req, tr => (tr, req, true)
  | f :: rest, req, tr =>
    match f.run req with
    | (req', .allow) => stepChain rest req' (tr ++ [f.fid])
    | (req', .deny _) => (tr ++ [f.fid], req', false)

/-- Run a route's filter chain on a request, from an empty trace. -/
def runChain (fs : List (Filter Req)) (req : Req) : List Nat × Req × Bool :=
  stepChain fs req []

/-! ### The accounting identity (generalized over the trace accumulator) -/

/-- If the handler is reached, the executed trace is the seed trace followed by
every configured id in order. -/
theorem stepChain_reached (fs : List (Filter Req)) :
    ∀ (req : Req) (tr : List Nat),
      (stepChain fs req tr).2.2 = true →
      (stepChain fs req tr).1 = tr ++ fs.map Filter.fid := by
  induction fs with
  | nil => intro req tr _; simp [stepChain]
  | cons f rest ih =>
    intro req tr hreached
    simp only [stepChain] at hreached ⊢
    cases hfr : f.run req with
    | mk req' d =>
      rw [hfr] at hreached
      cases d with
      | allow =>
        dsimp only at hreached ⊢
        rw [ih req' (tr ++ [f.fid]) hreached]
        simp
      | deny reason =>
        dsimp only at hreached
        simp at hreached

/-- In every outcome, the executed trace is the seed trace followed by a prefix
of the configured ids. -/
theorem stepChain_prefix (fs : List (Filter Req)) :
    ∀ (req : Req) (tr : List Nat),
      (stepChain fs req tr).1 <+: tr ++ fs.map Filter.fid := by
  induction fs with
  | nil => intro req tr; simp [stepChain]
  | cons f rest ih =>
    intro req tr
    simp only [stepChain]
    cases hfr : f.run req with
    | mk req' d =>
      cases d with
      | allow =>
        dsimp only
        have := ih req' (tr ++ [f.fid])
        simpa using this
      | deny reason =>
        dsimp only
        have hrw : tr ++ (f :: rest).map Filter.fid
            = (tr ++ [f.fid]) ++ rest.map Filter.fid := by simp
        rw [hrw]
        exact List.prefix_append _ _

/-! ### Corollaries on `runChain` -/

/-- **Chain-completeness (the accounting identity).** Any request that reaches
the handler has executed each configured filter exactly once, in configured
order: the trace equals `fs.map Filter.fid`. -/
theorem runChain_reached_trace {fs : List (Filter Req)} {req : Req}
    (h : (runChain fs req).2.2 = true) :
    (runChain fs req).1 = fs.map Filter.fid := by
  unfold runChain
  have := stepChain_reached fs req [] h
  simpa using this

/-- **The trace is always a prefix of the configured ids** — no unconfigured
filter runs, order is preserved, and a `deny` merely stops early. -/
theorem runChain_trace_prefix (fs : List (Filter Req)) (req : Req) :
    (runChain fs req).1 <+: fs.map Filter.fid := by
  unfold runChain
  have := stepChain_prefix fs req []
  simpa using this

/-- **No skipped filter.** When the handler is reached, every configured
filter's id is present in the trace. -/
theorem runChain_no_skip {fs : List (Filter Req)} {req : Req}
    (h : (runChain fs req).2.2 = true) {f : Filter Req} (hf : f ∈ fs) :
    f.fid ∈ (runChain fs req).1 := by
  rw [runChain_reached_trace h]
  exact List.mem_map_of_mem Filter.fid hf

/-- **No doubled filter.** When the handler is reached and the configured ids
are distinct, the executed trace has no duplicates. -/
theorem runChain_reached_nodup {fs : List (Filter Req)} {req : Req}
    (hnd : (fs.map Filter.fid).Nodup)
    (h : (runChain fs req).2.2 = true) :
    (runChain fs req).1.Nodup := by
  rw [runChain_reached_trace h]; exact hnd

/-- **Bounded on deny.** The trace never exceeds the configured id count. -/
theorem runChain_trace_length_le (fs : List (Filter Req)) (req : Req) :
    (runChain fs req).1.length ≤ fs.length := by
  have hp := runChain_trace_prefix fs req
  have := hp.length_le
  simpa using this

end Route.Chain
