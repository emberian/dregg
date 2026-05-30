/-
# Dregg2.Resource — resources beyond numbers: the resource-algebra (camera) tier.

`Core.lean` conserves a measure valued in a commutative monoid `M` (`count : Cell → M`,
`count B = count A + val tag`). That ALREADY covers far more than "numbers summing":
multi-asset (`M = K → ℕ`), fractional/continuous (`ℚ≥0`), debt/credit (`ℤ`). But a
monoid measure — "a quantity that adds" — cannot express the resources whose very
*composition is partial*, i.e. can be **invalid**:

  * **NFTs / linear tokens** — two holders cannot both hold the same unique id (Move's
    linear resources, Wadler's linear logic): composing overlapping holdings is INVALID,
    not summed. There is no "amount" to add — only existence, exclusively held.
  * **fractional permissions** — shares compose only while the total `≤ 1` (Boyland):
    `½ · ½ = 1` is valid (full), `1 · ¼` is INVALID (over-share).
  * **authoritative ↔ fragment** — a sovereign cell's TRUE balance `● a` versus each
    holder's partial view `◦ b`, where `◦ b` is valid only when `b ≼ a`. This is *exactly*
    the sovereign-cell / holder split (Iris `auth`), not a sum.
  * **capabilities themselves** — a cap is a resource; "authority never grows" is
    monotonicity under composition in a resource algebra. So `Authority.Positional`'s
    confinement law and `Core`'s conservation law are, at this tier, the SAME law.

The unifying structure is Iris's **camera** (a partial commutative monoid with a
validity predicate `valid` and a partial `core` for the duplicable/persistent part),
and the general conservation law is the **frame-preserving update**
`a ↝ b ≜ ∀ f, valid (a · f) → valid (b · f)`: "replacing `a` by `b` never invalidates
any frame `f` a third party might hold." Sum-conservation (`Core`) is the special case
`R = (ℕ, +)`, `valid ≡ ⊤`, where every update that keeps the global sum is an FPU.
The prize (Jung et al., *Iris from the Ground Up*, JFP 2018): ghost state and
permissions live in ONE algebra, so conservation and authority unify.

## Two modes — the camera is FULL; the ZK constraint binds only ONE fragment
dregg2 runs resources in two registers, mirroring the caps↔keys split:
  * **runtime / intra-vat (caps-as-caps):** live, mediator-enforced interactions where
    the kernel/vat IS the validity oracle. Here `valid` is just a predicate the runtime
    checks — NO circuit, NO succinctness constraint. The FULL camera (any `valid`, any
    `·`) is admissible; this is the canonical resource semantics of the system.
  * **attested / cross-vat (keys-as-caps):** a resource crossing a vat boundary as a
    proof-carrying certificate. ONLY here must `valid` be an in-circuit `Verify`
    (`Laws.lean`) — succinctly checkable (a field sum, sum-`≤`-1, a sorted-id accumulator,
    a Pedersen `●/◦` opening). This is a *sub-camera* (the succinctly-verifiable fragment),
    NOT a ceiling on the metatheory.
So: do NOT restrict the camera to the ZK-able fragment — that was a category error. The
metatheory models the whole system (runtime + proof-carrying); the verifier constrains
only what may travel as an attested cross-vat certificate. (This is the resource-tier
shadow of `dregg2.md §3` caps-as-caps vs keys-as-caps.)

## "Full camera" vs what is here
This module is a *discrete* resource algebra (RA): partial commutative monoid + `valid`
+ a `core` satisfying the three core laws (`core_id`/`core_idem`/`core_mono`). A *full*
Iris **camera** additionally carries a step-indexed OFE (`≡{n}≡`), non-expansive
`op`/`valid`/`core`, and the extension axiom — machinery needed ONLY for *higher-order /
recursive* resources (a cap that stores an invariant about another cell; resources
inside the coinductive `νF`). When dregg2 needs those, the camera's step-index should be
the SAME `▶` ("later") as `Boundary.lean`'s guard — exactly how Iris builds `iProp` as a
guarded fixpoint over cameras. Until then the discrete RA is the canonical tier.

Style: spec-first. The `ℕ` and `Excl` cameras are proved in full (including the core
laws); `Auth` gives concrete data with its laws `sorry`'d (the obligations to discharge
when the authoritative resource kind is admitted).
-/
import Mathlib.Algebra.Group.Defs

namespace Dregg2.Resource

universe u

/-- **A resource algebra (Iris camera, discrete/simplified).** A partial commutative
monoid: `op` is the composition `·`, `valid` carves out the admissible elements (the
partiality), `core` extracts the duplicable/persistent part (`none` = nothing
persistent). No unit is required (cameras need not be unital). -/
class ResourceAlgebra (R : Type u) where
  /-- Composition `a · b` (defined everywhere; partiality is carried by `valid`). -/
  op    : R → R → R
  /-- The validity predicate — the heart of partiality (NFT disjointness, frac `≤ 1`). -/
  valid : R → Prop
  /-- The core `|a|` — the part of `a` that may be freely duplicated; `none` = none. -/
  core  : R → Option R
  /-- `·` is commutative. -/
  op_comm  : ∀ a b, op a b = op b a
  /-- `·` is associative. -/
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c)
  /-- Validity is downward-closed under composition: a valid composite has valid parts
  (Iris camera axiom — you cannot manufacture validity by adding a frame). -/
  valid_op_left : ∀ a b, valid (op a b) → valid a
  /-- **core-id** (`|a| · a = a`): the core is a left-identity for its own element. -/
  core_id : ∀ a ca, core a = some ca → op ca a = a
  /-- **core-idem** (`||a|| = |a|`): the core is idempotent. -/
  core_idem : ∀ a ca, core a = some ca → core ca = some ca
  /-- **core-mono** (`a ≼ b → |a| ≼ |b|`): the core is monotone along the extension
  order `≼` (`a ≼ b ≜ ∃ c, b = a · c`). -/
  core_mono : ∀ a b ca, core a = some ca → (∃ c, b = op a c) →
                ∃ cb, core b = some cb ∧ ∃ d, cb = op ca d

namespace ResourceAlgebra
@[inherit_doc] scoped infixl:70 " ⊙ " => ResourceAlgebra.op
end ResourceAlgebra

open ResourceAlgebra

/-- **The frame-preserving update** `a ↝ b`: replacing `a` by `b` keeps every frame `f`
that was compatible with `a` compatible with `b`. THIS is the general conservation law;
"the global sum is preserved" is its `(ℕ,+)` shadow. -/
def Fpu {R : Type u} [ResourceAlgebra R] (a b : R) : Prop :=
  ∀ f : R, valid (a ⊙ f) → valid (b ⊙ f)

/-- **General conservation.** An ordinary turn's effect on the cell's resource is a
frame-preserving update — it must not invalidate any third party's holding. (Mint/burn
are the generators permitted to *not* be FPUs in the trivial direction; they are FPUs
relative to the explicit `● authoritative` balance, which absorbs the change.) -/
def ConservesResource {R : Type u} [ResourceAlgebra R] (pre post : R) : Prop :=
  Fpu pre post

/-- `↝` is reflexive: doing nothing is frame-preserving. -/
theorem Fpu.refl {R : Type u} [ResourceAlgebra R] (a : R) : Fpu a a :=
  fun _ h => h

/-- `↝` is transitive. -/
theorem Fpu.trans {R : Type u} [ResourceAlgebra R] {a b c : R}
    (hab : Fpu a b) (hbc : Fpu b c) : Fpu a c :=
  fun f h => hbc f (hab f h)

/-! ## Instance 1 — `ℕ` under `+`: the bridge to `Core`'s sum-conservation. -/

/-- `(ℕ, +)` as a (total, always-valid) camera: this is exactly `Core.Conservation`
seen as a resource algebra. Everything is valid; the core is the unit `0` (the only
freely-duplicable element). Proven in full. -/
instance : ResourceAlgebra Nat where
  op    := (· + ·)
  valid := fun _ => True
  core  := fun _ => some 0
  op_comm  := Nat.add_comm
  op_assoc := Nat.add_assoc
  valid_op_left := fun _ _ _ => trivial
  core_id := by rintro a ca h; rw [Option.some.injEq] at h; subst h; exact Nat.zero_add a
  core_idem := by intro a ca h; exact h
  core_mono := by
    rintro a b ca h _; rw [Option.some.injEq] at h; subst h
    exact ⟨0, rfl, 0, (Nat.add_zero 0).symm⟩

/-- In a total, always-valid camera (like `ℕ`) *every* update is frame-preserving:
there are no third-party constraints to break. The non-triviality of conservation lives
entirely in `valid` — which is why richer cameras (frac, NFT, auth) are where the law
bites. -/
theorem fpu_of_total {R : Type u} [ResourceAlgebra R]
    (htotal : ∀ x : R, valid x) (a b : R) : Fpu a b :=
  fun f _ => htotal (b ⊙ f)

/-! ## Instance 2 — `Excl`: the exclusive (NFT / linear-token) camera.

`Ex a` is held by exactly one party; two `Ex` never compose (`Ex a ⊙ Ex b = invalid`),
which is precisely **non-duplication** — the structural fact behind NFTs and Move's
linear resources. There is no "amount": the conserved content is *unique existence*. -/

/-- The exclusive camera carrier: a held unique value, or the invalidity bottom. -/
inductive Excl (R : Type u) : Type u where
  | ex : R → Excl R
  | invalid
  deriving Repr

/-- Composition of exclusives: any composition of two held values is `invalid` (you
cannot hold the same unique resource twice); `invalid` is absorbing. -/
def Excl.op {R : Type u} : Excl R → Excl R → Excl R
  | _, _ => Excl.invalid

/-- An exclusive is valid iff it is an actually-held value (never `invalid`). -/
def Excl.valid {R : Type u} : Excl R → Prop
  | .ex _    => True
  | .invalid => False

instance {R : Type u} : ResourceAlgebra (Excl R) where
  op    := Excl.op
  valid := Excl.valid
  core  := fun _ => none          -- nothing exclusive is duplicable: empty core
  op_comm  := by intro a b; rfl   -- both sides are `invalid`
  op_assoc := by intro a b c; rfl -- all compositions collapse to `invalid`
  -- `op a b = invalid` is never `valid`, so the hypothesis is vacuous.
  valid_op_left := by intro a b h; exact absurd h (by simp [Excl.op, Excl.valid])
  -- the empty core (`none`) makes all three core laws vacuously true.
  core_id := by intro a ca h; simp at h
  core_idem := by intro a ca h; simp at h
  core_mono := by intro a b ca h _; simp at h

/-- **Non-duplication, proved.** No exclusive resource composes with itself validly —
the camera-level statement that an NFT cannot be in two places. -/
theorem excl_no_dup {R : Type u} (a : Excl R) : ¬ valid (a ⊙ a) := by
  simp [ResourceAlgebra.op, ResourceAlgebra.valid, Excl.op, Excl.valid]

/-! ## Instance 3 — `Auth`: the authoritative ↔ fragment camera (the sovereign split).

**This is where conservation and authority become the same law.** A sovereign cell
holds the **authoritative** total `● a : M`; each holder holds a **fragment** `◦ f : M`,
valid only when `f ≼ a` (the fragment fits within the authority). The authoritative slot
is *exclusive* (two `●` never compose — like an NFT on the total), while fragments add.
This is exactly the cell's true balance vs each holder's partial view (Mina's account
vs zkApp-command local view; Iris's `auth M`), and "the sum is conserved" is precisely
*"the authoritative total is preserved while fragments rearrange within it"* — an FPU on
`Auth M`. -/

section Auth
variable {M : Type u} [AddCommMonoid M]

/-- Monoid **extension order**: `fits f a` iff `a = f + c` for some remainder `c` — the
fragment `f` fits within the authority `a` (no order typeclass needed; the monoid
generates its own `≼`). -/
def fits (f a : M) : Prop := ∃ c, a = f + c

/-- The authoritative↔fragment carrier: an optional authoritative total plus an owned
fragment, or the invalidity bottom (reached by composing two authoritatives). -/
inductive Auth (M : Type u) where
  | mk (auth : Option M) (frag : M)
  | invalid

/-- Composition: fragments add; at most one authoritative may be present (two ⇒
`invalid`); `invalid` is absorbing. -/
def Auth.op : Auth M → Auth M → Auth M
  | .invalid, _ => .invalid
  | _, .invalid => .invalid
  | .mk a1 f1, .mk a2 f2 =>
      match a1, a2 with
      | none,   a      => .mk a (f1 + f2)
      | a,      none    => .mk a (f1 + f2)
      | some _, some _  => .invalid

/-- Validity: `invalid` is never valid; a pure fragment is always valid; an
authoritative element is valid iff its fragment fits within its total. -/
def Auth.valid : Auth M → Prop
  | .invalid       => False
  | .mk none _     => True
  | .mk (some a) f => fits f a

instance : ResourceAlgebra (Auth M) where
  op    := Auth.op
  valid := Auth.valid
  core  := fun _ => some (.mk none 0)   -- the empty fragment: the duplicable unit
  op_comm  := by
    intro a b
    cases a with
    | invalid => cases b <;> rfl
    | mk a1 f1 =>
      cases b with
      | invalid => rfl
      | mk a2 f2 =>
        cases a1 <;> cases a2 <;> simp [Auth.op, add_comm]
  op_assoc := by
    intro a b c
    cases a with
    | invalid => rfl
    | mk a1 f1 =>
      cases b with
      | invalid => cases c <;> rfl
      | mk a2 f2 =>
        cases c with
        | invalid => cases a1 <;> cases a2 <;> rfl
        | mk a3 f3 =>
          cases a1 <;> cases a2 <;> cases a3 <;>
            simp [Auth.op, add_assoc]
  valid_op_left := by
    intro a b h
    cases a with
    | invalid => exact absurd h (by cases b <;> simp [Auth.op, Auth.valid])
    | mk a1 f1 =>
      cases b with
      | invalid => exact absurd h (by simp [Auth.op, Auth.valid])
      | mk a2 f2 =>
        cases a1 with
        | none => simp [Auth.valid]
        | some a1 =>
          cases a2 with
          | none =>
            -- op = mk (some a1) (f1+f2), valid means fits (f1+f2) a1
            simp only [Auth.op, Auth.valid, fits] at h ⊢
            obtain ⟨c, hc⟩ := h
            exact ⟨f2 + c, by rw [hc, add_assoc]⟩
          | some a2 =>
            -- op = invalid, h : False
            exact absurd h (by simp [Auth.op, Auth.valid])
  core_id := by
    intro a ca h
    rw [Option.some.injEq] at h; subst h
    cases a with
    | invalid => rfl
    | mk a1 f1 =>
      cases a1 <;> simp [Auth.op, zero_add]
  core_idem := by intro a ca h; rw [Option.some.injEq] at h; subst h; rfl
  core_mono := by
    intro a b ca h _
    rw [Option.some.injEq] at h; subst h
    exact ⟨.mk none 0, rfl, .mk none 0, by simp [Auth.op, add_zero]⟩

/-- **CANONICAL conservation law: conservation = a frame-preserving update on the
authoritative camera.** Moving a holder's fragment `f → f'` under a *fixed* sovereign
total `a` is frame-preserving exactly when it does not enlarge what any frame needs
(`hmono`). This is the honest statement the bare-sum law hides: a *withdrawal* (`f' ≼ f`)
is always conservative; a *deposit* is conservative only against the authority's
headroom. "Σ in = Σ out" is the special case where `hmono` holds by an exact swap. -/
theorem conservation_is_fpu (a f f' : M)
    (hmono : ∀ g, fits (f + g) a → fits (f' + g) a) :
    Fpu (R := Auth M) (.mk (some a) f) (.mk (some a) f') := by
  intro fr h
  cases fr with
  | invalid => exact absurd h (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])
  | mk a2 f2 =>
    cases a2 with
    | none =>
      -- op (mk (some a) f) (mk none f2) = mk (some a) (f + f2); valid = fits (f + f2) a
      simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid] at h ⊢
      exact hmono f2 h
    | some a2 =>
      -- both authoritative ⇒ op = invalid ⇒ h : False
      exact absurd h (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])

/-- **Authority IS conservation (the unification — a definition, not a vacuous lemma).**
"Authority never grows beyond the policy" (`Authority.Positional.confinement_preserved`)
is the SAME predicate as conservation: confinement of `held` by `held'` is *literally*
`Fpu held' held` in the camera whose elements are capabilities (`valid` = "within the
policy upper bound"). Defining it as `Fpu` — rather than proving an `↔` — is the point:
at the camera tier `Core`'s conservation law and `Authority`'s confinement law are one
law (Iris: ghost state and permissions share one algebra). -/
def ConfinesAuthority {C : Type u} [ResourceAlgebra C] (held' held : C) : Prop :=
  Fpu held' held

end Auth

end Dregg2.Resource
