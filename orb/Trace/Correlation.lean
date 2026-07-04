/-
Trace.Correlation — assigning a correlation id to an inbound request, and
propagating it onto the upstream request.

The transition system is deliberately small.  An `Inbound` request may already
carry a correlation id in its header (the client-supplied value) and always
carries a generator `seed` — the id generator's only input.  `assign` decides
the id:

  * when the assignment policy trusts the inbound id and one is present, adopt
    it;
  * otherwise generate a fresh id, `gen seed`, a pure function of the seed.

`process` records the assigned id in a `Processed` state whose single `corr`
field means the request carries *exactly one* correlation id by construction.
`inject` places that id into the upstream request's header; `upstreamCorr`
reads it back — modelling that the upstream actually *sees* the id, not just
that a projection is copied.

Headline results:

  * `process_carries_one` (**theorem 1**) — every processed request carries
    exactly one correlation id (`∃!`).  Totality: `assign_total`; determinism
    given the generator input: `assign_deterministic` / `process_deterministic`.
  * `inject_faithful` / `upstream_sees_request_corr` (**theorem 2**) — the id
    read off the upstream request equals the request's correlation id.
-/

import Trace.Basic

namespace Trace

/-- A correlation id.  Modelled as an opaque byte string; only equality is
used. -/
abbrev CorrId := List Nat

/-- The correlation-header name carried on the wire. -/
def corrHeader : String := "x-correlation-id"

/-- Assignment policy: when `true`, an inbound id is adopted; when `false`, a
fresh id is always generated. -/
abbrev Trust := Bool

/-- An inbound request.  It may already carry a correlation id in its header
(the client-supplied value), and always carries the generator seed that is the
sole input to a freshly generated id. -/
structure Inbound where
  /-- The correlation id present on the inbound request, if any. -/
  carried : Option CorrId
  /-- The generator seed for this request. -/
  seed : CorrId
deriving Repr, DecidableEq

/-- A processed request: it carries exactly one correlation id, structurally. -/
structure Processed where
  /-- The single, assigned correlation id. -/
  corr : CorrId
deriving Repr, DecidableEq

/-- The upstream request: a header assoc-list the correlation id is injected
into. -/
structure UpReq where
  /-- Header key/value pairs on the upstream request. -/
  headers : List (String × CorrId)
deriving Repr

/-- Assign a correlation id.  Total: it always yields exactly one id.  Adoption
when the policy trusts the inbound id and one is present; generation from the
seed otherwise. `gen` is a pure function — the id it produces is fully
determined by its input. -/
def assign (gen : CorrId → CorrId) (trust : Trust) (carried : Option CorrId)
    (seed : CorrId) : CorrId :=
  match trust, carried with
  | true, some id => id
  | _, _ => gen seed

/-- Process an inbound request into a state carrying its assigned id. -/
def process (gen : CorrId → CorrId) (trust : Trust) (r : Inbound) : Processed :=
  { corr := assign gen trust r.carried r.seed }

/-- Inject the assigned correlation id into the upstream request's header. -/
def inject (p : Processed) : UpReq :=
  { headers := [(corrHeader, p.corr)] }

/-- Read the correlation id off an upstream request. -/
def upstreamCorr (u : UpReq) : Option CorrId :=
  (u.headers.find? (fun kv => kv.1 == corrHeader)).map (fun kv => kv.2)

/-! ### Assignment: totality and case characterization -/

/-- Assignment always yields an id (totality). -/
theorem assign_total (gen : CorrId → CorrId) (trust : Trust) (carried : Option CorrId)
    (seed : CorrId) : ∃ id, assign gen trust carried seed = id :=
  ⟨_, rfl⟩

/-- Adoption: a trusted, present inbound id is the assigned id. -/
theorem assign_adopt (gen : CorrId → CorrId) (id seed : CorrId) :
    assign gen true (some id) seed = id := rfl

/-- Generation: an untrusted request always gets the generated id. -/
theorem assign_gen_of_untrusted (gen : CorrId → CorrId) (carried : Option CorrId)
    (seed : CorrId) : assign gen false carried seed = gen seed := by
  cases carried <;> rfl

/-- Generation: an absent inbound id always yields the generated id. -/
theorem assign_gen_of_absent (gen : CorrId → CorrId) (trust : Trust) (seed : CorrId) :
    assign gen trust none seed = gen seed := by
  cases trust <;> rfl

/-- Determinism given the generator input: fixing the seed fixes the id — the
seed is the only source of nondeterminism. -/
theorem assign_deterministic (gen : CorrId → CorrId) (trust : Trust)
    (carried : Option CorrId) {seed₁ seed₂ : CorrId} (hseed : seed₁ = seed₂) :
    assign gen trust carried seed₁ = assign gen trust carried seed₂ := by
  rw [hseed]

/-- Processing is a function of its inputs (full determinism). -/
theorem process_deterministic (gen : CorrId → CorrId) (trust : Trust)
    {r₁ r₂ : Inbound} (h : r₁ = r₂) : process gen trust r₁ = process gen trust r₂ := by
  rw [h]

/-! ### Theorem 1 — every processed request carries exactly one id -/

/-- **Theorem 1.**  After assignment, a processed request carries exactly one
correlation id: there is an id it carries, and any id it carries is that one.
(`∃!` unfolded, since core Lean has no `ExistsUnique`.) -/
theorem process_carries_one (gen : CorrId → CorrId) (trust : Trust) (r : Inbound) :
    ∃ id, (process gen trust r).corr = id
        ∧ ∀ id', (process gen trust r).corr = id' → id' = id :=
  ⟨(process gen trust r).corr, rfl, fun _ hy => hy.symm⟩

/-! ### Theorem 2 — propagation faithfulness -/

/-- **Theorem 2 (propagation faithfulness).**  The correlation id read off the
upstream request equals the id injected — the upstream sees the same id. -/
theorem inject_faithful (p : Processed) : upstreamCorr (inject p) = some p.corr := by
  simp [upstreamCorr, inject, corrHeader]

/-- End-to-end: the upstream request built from a processed request exposes
that request's correlation id. -/
theorem upstream_sees_request_corr (gen : CorrId → CorrId) (trust : Trust) (r : Inbound) :
    upstreamCorr (inject (process gen trust r)) = some (process gen trust r).corr :=
  inject_faithful _

end Trace
