import Dsl.Component

/-!
# The four primitives as components

Each of the four DSL primitive shapes is a `Component`, so the composition laws
of `Dsl.Component` apply to all of them uniformly. Concrete, deep properties of
each shape live in the dedicated libraries (`Arena` for region, `Proto` and the
protocol FSMs for machine, `Uring`/`Pool` for linear, the concurrency twins for
shared); the point here is that the four shapes share the component structure
and therefore *compose* — a machine carrying a region and holding a linear
resource is itself a component whose invariant is preserved on every reachable
state, with no re-proof.
-/

namespace Dsl
namespace Primitives

/-! ## region — an immutable byte store with in-bounds views -/

structure Store where
  bytes : List UInt8
  views : List (Nat × Nat)

def Store.wf (s : Store) : Prop := ∀ v ∈ s.views, v.1 + v.2 ≤ s.bytes.length

/-- Register a view; keep it only if it lands in bounds (else a no-op). -/
def regionStep (s : Store) (v : Nat × Nat) : Store :=
  if v.1 + v.2 ≤ s.bytes.length then { s with views := v :: s.views } else s

def region : Component where
  State := Store
  Input := Nat × Nat
  Output := Unit
  inv := Store.wf
  init := { bytes := [0, 1, 2, 3], views := [] }
  step := fun s v => (regionStep s v, [])
  init_wf := by intro v hv; simp at hv
  step_wf := by
    intro s v h
    show Store.wf (regionStep s v)
    unfold regionStep
    split
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · assumption
      · exact h w hw'
    · exact h

/-! ## machine — a sans-IO transition system (here: a saturating counter) -/

structure Ctr where
  val : Nat
  cap : Nat

def Ctr.wf (c : Ctr) : Prop := c.val ≤ c.cap

def machine : Component where
  State := Ctr
  Input := Unit
  Output := Nat
  inv := Ctr.wf
  init := { val := 0, cap := 8 }
  step := fun c _ => let c' := { c with val := min (c.val + 1) c.cap }; (c', [c'.val])
  init_wf := by simp [Ctr.wf]
  step_wf := by
    intro c _ _
    show min (c.val + 1) c.cap ≤ c.cap
    exact Nat.min_le_right _ _

/-! ## linear — acquire → use → release-once -/

inductive Life where
  | fresh
  | held
  | released
deriving DecidableEq, Repr

inductive LinOp where
  | acquire
  | use
  | release
deriving Repr

/-- The linear lifecycle. Illegal operations (use before acquire, anything after
release) are no-ops, so the discipline is total; `released` is absorbing. -/
def linStep : Life → LinOp → Life
  | .fresh, .acquire => .held
  | .held, .use => .held
  | .held, .release => .released
  | s, _ => s

def linear : Component where
  State := Life
  Input := LinOp
  Output := Unit
  inv := fun _ => True
  init := .fresh
  step := fun s op => (linStep s op, [])
  init_wf := trivial
  step_wf := fun _ _ _ => trivial

/-- **Release-once.** A released resource stays released — no operation reuses
or re-acquires it (the linear discipline's safety property). -/
theorem released_absorbing (op : LinOp) : linStep .released op = .released := by
  cases op <;> rfl

/-- Use is only effective while held; it never resurrects a released resource. -/
theorem no_use_after_release : linStep .released .use = .released := rfl

/-! ## shared — a concurrent object with a declared invariant (here: a counter
capped by a declared bound) -/

structure SharedCtr where
  val : Nat
  bound : Nat

/-- The declared invariant: the value stays within the bound. -/
def SharedCtr.inv (c : SharedCtr) : Prop := c.val ≤ c.bound

/-- An operation that increments only while under the bound (a saturating,
invariant-preserving op — the sequential image of the shared object). -/
def sharedStep (c : SharedCtr) (_ : Unit) : SharedCtr :=
  if c.val < c.bound then { c with val := c.val + 1 } else c

def shared : Component where
  State := SharedCtr
  Input := Unit
  Output := Nat
  inv := SharedCtr.inv
  init := { val := 0, bound := 8 }
  step := fun c _ => let c' := sharedStep c (); (c', [c'.val])
  init_wf := by simp [SharedCtr.inv]
  step_wf := by
    intro c _ h
    show SharedCtr.inv (sharedStep c ())
    unfold sharedStep
    split
    · rename_i hlt; simp only [SharedCtr.inv]; omega
    · exact h

/-! ## The four compose -/

/-- The full stack: a machine carrying a region, holding a linear resource,
alongside a shared object — assembled by the component product. -/
def full : Component :=
  region.prod (machine.prod (linear.prod shared))

/-- **The composition theorem, instantiated.** Every reachable state of the
four-primitive composite satisfies the conjoined invariant — in-bounds region,
well-formed machine, valid linear lifecycle, and the shared object's declared
invariant all hold together, on every reachable state, with no re-proof beyond
the per-primitive `step_wf`. -/
theorem full_reachable_wf (s : full.State) (h : full.Reachable s) : full.inv s :=
  full.reachable_inv h

/-- Unfolded: each factor's invariant holds on its projection of a reachable
composite state. -/
theorem full_factors_wf (s : full.State) (h : full.Reachable s) :
    region.inv s.1 ∧ machine.inv s.2.1 ∧ (linear.inv s.2.2.1 ∧ shared.inv s.2.2.2) := by
  have := full_reachable_wf s h
  exact this

end Primitives
end Dsl
