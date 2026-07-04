/-
Acme.Order — the order lifecycle FSM (RFC 8555 §7.1.6).

An order carries a list of authorization statuses and an order status. The
lifecycle is

    pending ──(all authorizations valid)──▶ ready
    pending ──(some authorization invalid)──▶ invalid
    ready   ──finalize (client submits CSR)──▶ processing
    processing ──issued (CA issued cert)──▶ valid          (terminal)
    processing ──issuanceFailed──▶ invalid                 (terminal)

The transition into `ready` is *gated*: it fires only when every
authorization is `valid` (`allValid`). Authorization statuses advance
monotonically (`setAuthzAt` only overwrites a `pending` entry), so once all
authorizations are valid they stay valid.

The load-bearing invariant is `Order.wf`: any order in `ready`, `processing`,
or `valid` has all authorizations valid. It is inductive under `orderStep`,
hence holds along every event sequence from a fresh order. Its instantiation
at `valid` is theorem (1)'s "no skipping": **a valid order — the one that
yields a certificate — has every authorization valid.**

Theorems:
  * `orderStep_total` / `orderStep_deterministic` — the transition relation is
    total and single-valued (the FSM is total and deterministic).
  * `valid_requires_all_authz_valid` — **no skipping authorization**: a
    reachable order at `valid` has `allValid` of its authorizations.
  * `into_valid` / `into_processing` / `into_ready` — the step-level ordering:
    the only predecessor of `valid` is `processing` via `issued`, of
    `processing` is `ready` via `finalize`, of `ready` is `pending`. No stage
    is skipped.
  * `valid_absorbing` / `valid_no_revert` / `valid_run_absorbing` /
    `no_valid_to_pending` — **monotone issuance**: a valid order never
    reverts; renewal after expiry is a *fresh* lifecycle (`Order.fresh`),
    never a transition out of `valid`.
-/

import Acme.Basic

namespace Acme

/-- An order: the statuses of its authorizations, and its own status. -/
structure Order where
  authzs : List AuthzStatus
  status : OrderStatus
deriving DecidableEq, Repr

/-- Advance authorization `i` to `valid`/`invalid` on a validation result —
but only if it is still `pending`. This makes authorization status monotone:
a terminal (valid/invalid) authorization is never overwritten. Out-of-range
`i` is a no-op. -/
def setAuthzAt (as : List AuthzStatus) (i : Nat) (ok : Bool) : List AuthzStatus :=
  match as[i]? with
  | some .pending => as.set i (if ok then .valid else .invalid)
  | _ => as

/-- Recompute the order status from the authorization statuses (used while
`pending`): promote to `ready` once all are valid, fail to `invalid` once any
is invalid, otherwise stay put. Only the status changes; the authorizations do
not. -/
def Order.recompute (o : Order) : Order :=
  if allValid o.authzs = true then { o with status := .ready }
  else if anyInvalid o.authzs = true then { o with status := .invalid }
  else o

/-- Order events. `authzResult i ok` is the CA's validation verdict on
authorization `i` (the named abstract interface, surfaced from
`Acme.Challenge`); `finalize` submits the CSR; `issued`/`issuanceFailed` are
the CA's issuance outcome. -/
inductive OrderEvent where
  | authzResult (i : Nat) (ok : Bool)
  | finalize
  | issued
  | issuanceFailed
deriving DecidableEq, Repr

/-- The order step. Total and deterministic; events that do not apply to the
current status stutter. `valid`/`invalid` are absorbing (catch-all). -/
def orderStep (o : Order) (e : OrderEvent) : Order :=
  match o.status, e with
  | .pending, .authzResult i ok =>
      Order.recompute { o with authzs := setAuthzAt o.authzs i ok }
  | .ready, .finalize => { o with status := .processing }
  | .processing, .issued => { o with status := .valid }
  | .processing, .issuanceFailed => { o with status := .invalid }
  | _, _ => o

/-! ### Totality and determinism -/

/-- The induced transition relation. -/
def OrderTrans (o : Order) (e : OrderEvent) (o' : Order) : Prop := orderStep o e = o'

/-- **Total.** Every configuration has a successor for every event. -/
theorem orderStep_total (o : Order) (e : OrderEvent) :
    ∃ o', OrderTrans o e o' := ⟨_, rfl⟩

/-- **Deterministic.** The successor is unique. -/
theorem orderStep_deterministic {o : Order} {e : OrderEvent} {o₁ o₂ : Order}
    (h₁ : OrderTrans o e o₁) (h₂ : OrderTrans o e o₂) : o₁ = o₂ :=
  h₁.symm.trans h₂

/-! ### `recompute`, characterized -/

/-- `recompute` never touches the authorization list. -/
theorem recompute_authzs (o : Order) : o.recompute.authzs = o.authzs := by
  unfold Order.recompute
  by_cases hv : allValid o.authzs = true
  · rw [if_pos hv]
  · rw [if_neg hv]
    by_cases hi : anyInvalid o.authzs = true
    · rw [if_pos hi]
    · rw [if_neg hi]

/-- The status after `recompute` is one of `ready`, `invalid`, or unchanged. -/
theorem recompute_status_mem (o : Order) :
    o.recompute.status = .ready ∨ o.recompute.status = .invalid
      ∨ o.recompute.status = o.status := by
  unfold Order.recompute
  by_cases hv : allValid o.authzs = true
  · rw [if_pos hv]; exact Or.inl rfl
  · rw [if_neg hv]
    by_cases hi : anyInvalid o.authzs = true
    · rw [if_pos hi]; exact Or.inr (Or.inl rfl)
    · rw [if_neg hi]; exact Or.inr (Or.inr rfl)

/-- Landing in `ready` via `recompute` (from a pending order) forces all
authorizations valid. -/
theorem recompute_ready_allValid {o : Order} (hp : o.status = .pending)
    (h : o.recompute.status = .ready) : allValid o.authzs = true := by
  unfold Order.recompute at h
  by_cases hv : allValid o.authzs = true
  · exact hv
  · exfalso
    rw [if_neg hv] at h
    by_cases hi : anyInvalid o.authzs = true
    · rw [if_pos hi] at h; simp at h
    · rw [if_neg hi] at h; rw [hp] at h; simp at h

theorem recompute_status_ne_valid {o : Order} (hp : o.status = .pending) :
    o.recompute.status ≠ .valid := by
  rcases recompute_status_mem o with hr | hr | hr <;> rw [hr] <;> simp_all

theorem recompute_status_ne_processing {o : Order} (hp : o.status = .pending) :
    o.recompute.status ≠ .processing := by
  rcases recompute_status_mem o with hr | hr | hr <;> rw [hr] <;> simp_all

/-! ### The well-formedness invariant -/

/-- **Invariant.** An order that has left `pending` for `ready`, `processing`,
or `valid` has every authorization valid. -/
def Order.wf (o : Order) : Prop :=
  o.status = .ready ∨ o.status = .processing ∨ o.status = .valid
    → allValid o.authzs = true

/-- `recompute` from a pending order preserves the invariant: the only way it
reaches `ready` is with all authorizations valid. -/
theorem recompute_wf {o : Order} (hp : o.status = .pending) : o.recompute.wf := by
  unfold Order.wf
  intro hs
  rw [recompute_authzs]
  rcases recompute_status_mem o with hr | hr | hr
  · exact recompute_ready_allValid hp hr
  · rw [hr] at hs; rcases hs with h | h | h <;> simp at h
  · rw [hr, hp] at hs; rcases hs with h | h | h <;> simp at h

/-- **The invariant is inductive.** Every `orderStep` preserves `Order.wf`. -/
theorem orderStep_wf {o : Order} {e : OrderEvent} (h : o.wf) :
    (orderStep o e).wf := by
  obtain ⟨as, st⟩ := o
  cases st <;> cases e <;>
    first
      | exact h
      | exact recompute_wf rfl
      | (intro hs; first
          | exact h (Or.inl rfl)
          | exact h (Or.inr (Or.inl rfl))
          | exact h (Or.inr (Or.inr rfl))
          | (rcases hs with h1 | h1 | h1 <;> simp_all))

/-! ### Reachability from a fresh order -/

/-- A fresh order for a set of identifiers: one `pending` authorization each,
order status `pending`. This is what certificate issuance — and renewal —
starts from. -/
def Order.fresh (identifiers : List Bytes) : Order :=
  { authzs := identifiers.map (fun _ => .pending), status := .pending }

/-- A fresh order is well-formed (vacuously — it is `pending`). -/
theorem Order.fresh_wf (ids : List Bytes) : (Order.fresh ids).wf := by
  unfold Order.wf
  intro hs
  simp [Order.fresh] at hs

/-- Fold the step over an event sequence. -/
def orderRun (o : Order) : List OrderEvent → Order
  | [] => o
  | e :: es => orderRun (orderStep o e) es

/-- The invariant survives any event sequence. -/
theorem orderRun_wf (o : Order) (h : o.wf) (es : List OrderEvent) :
    (orderRun o es).wf := by
  induction es generalizing o with
  | nil => exact h
  | cons e es ih => exact ih (orderStep o e) (orderStep_wf h)

/-- **No skipping authorization (theorem 1).** Any order reachable from a
fresh order that has reached `valid` — the status at which a certificate is
issued — has *every* authorization valid. A certificate is never issued past a
pending or failed authorization. -/
theorem valid_requires_all_authz_valid (ids : List Bytes) (es : List OrderEvent)
    (h : (orderRun (Order.fresh ids) es).status = .valid) :
    allValid (orderRun (Order.fresh ids) es).authzs = true :=
  orderRun_wf (Order.fresh ids) (Order.fresh_wf ids) es (Or.inr (Or.inr h))

/-! ### Step-level ordering: no stage is skipped -/

/-- The only predecessor of `valid` is `processing` via `issued` (or `valid`
itself). -/
theorem into_valid {o : Order} {e : OrderEvent}
    (h : (orderStep o e).status = .valid) :
    o.status = .valid ∨ (o.status = .processing ∧ e = .issued) := by
  obtain ⟨as, st⟩ := o
  cases st
  · cases e
    · exact absurd h (recompute_status_ne_valid rfl)
    · simp [orderStep] at h
    · simp [orderStep] at h
    · simp [orderStep] at h
  · cases e <;> simp [orderStep] at h
  · cases e
    · simp [orderStep] at h
    · simp [orderStep] at h
    · exact Or.inr ⟨rfl, rfl⟩
    · simp [orderStep] at h
  · exact Or.inl rfl
  · cases e <;> simp [orderStep] at h

/-- The only predecessor of `processing` is `ready` via `finalize` (or
`processing` itself). -/
theorem into_processing {o : Order} {e : OrderEvent}
    (h : (orderStep o e).status = .processing) :
    o.status = .processing ∨ (o.status = .ready ∧ e = .finalize) := by
  obtain ⟨as, st⟩ := o
  cases st
  · cases e
    · exact absurd h (recompute_status_ne_processing rfl)
    · simp [orderStep] at h
    · simp [orderStep] at h
    · simp [orderStep] at h
  · cases e
    · simp [orderStep] at h
    · exact Or.inr ⟨rfl, rfl⟩
    · simp [orderStep] at h
    · simp [orderStep] at h
  · exact Or.inl rfl
  · cases e <;> simp [orderStep] at h
  · cases e <;> simp [orderStep] at h

/-- The only predecessor of `ready` is `pending` (or `ready` itself). -/
theorem into_ready {o : Order} {e : OrderEvent}
    (h : (orderStep o e).status = .ready) :
    o.status = .ready ∨ o.status = .pending := by
  obtain ⟨as, st⟩ := o
  cases st
  · exact Or.inr rfl
  · exact Or.inl rfl
  · cases e <;> simp [orderStep] at h
  · cases e <;> simp [orderStep] at h
  · cases e <;> simp [orderStep] at h

/-! ### Monotone issuance: no revert -/

/-- **A valid order is absorbing.** Every event stutters. -/
theorem valid_absorbing {o : Order} (h : o.status = .valid) (e : OrderEvent) :
    orderStep o e = o := by
  obtain ⟨as, st⟩ := o
  simp only at h
  subst h
  cases e <;> rfl

/-- **No revert.** A valid order stays valid under any event. -/
theorem valid_no_revert {o : Order} (h : o.status = .valid) (e : OrderEvent) :
    (orderStep o e).status = .valid := by
  rw [valid_absorbing h]; exact h

/-- An invalid order is likewise absorbing. -/
theorem invalid_absorbing {o : Order} (h : o.status = .invalid) (e : OrderEvent) :
    orderStep o e = o := by
  obtain ⟨as, st⟩ := o
  simp only at h
  subst h
  cases e <;> rfl

/-- **Monotone over sequences.** A valid order is fixed by any event sequence:
issuance never reverts, no matter what follows. -/
theorem valid_run_absorbing {o : Order} (h : o.status = .valid)
    (es : List OrderEvent) : orderRun o es = o := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      show orderRun (orderStep o e) es = o
      rw [valid_absorbing h]
      exact ih

/-- A valid order never transitions back to `pending`: renewal is not a
back-edge in this FSM. -/
theorem no_valid_to_pending {o : Order} (h : o.status = .valid) (e : OrderEvent) :
    (orderStep o e).status ≠ .pending := by
  rw [valid_absorbing h, h]
  decide

/-! ### Renewal is a fresh lifecycle -/

/-- Renewal after expiry starts a brand-new order. There is no transition from
`valid` (or from an expired certificate) back into the lifecycle; the model
represents renewal as constructing a fresh order. This is the same
`Order.fresh` used for first issuance. -/
def Order.renew (identifiers : List Bytes) : Order := Order.fresh identifiers

/-- A renewed order starts `pending` (a full new lifecycle), not at any
inherited later stage. -/
theorem renew_starts_pending (ids : List Bytes) :
    (Order.renew ids).status = .pending := rfl

/-- Every authorization of a fresh/renewed order starts `pending` — no
authorization is inherited as already valid. -/
theorem fresh_all_pending (ids : List Bytes) :
    ∀ a ∈ (Order.fresh ids).authzs, a = AuthzStatus.pending := by
  intro a ha
  simp only [Order.fresh, List.mem_map] at ha
  obtain ⟨_, _, h⟩ := ha
  exact h.symm

end Acme
