/-!
# Per-tenant / per-exposure isolation as a capability partition

Each tenant holds a capability scoping the resources it owns; each exposure is
bound to exactly one tenant; a request on an exposure may touch only resources
in its tenant's scope. This is the isolation security property: with disjoint
tenant scopes, a request served under one tenant provably never reaches another
tenant's resources.
-/

namespace Isolation

abbrev TenantId := Nat
abbrev ExposureId := Nat
abbrev ResourceId := Nat

/-- A configured system: a per-tenant scope predicate, the exposure→tenant
binding, and the resources each exposure's request touches, together with the
well-formedness fact that the router respects the partition. -/
structure System where
  /-- Which resources a tenant's capability scopes. -/
  scope : TenantId → ResourceId → Bool
  /-- The exposure→tenant binding (a total function: one tenant per exposure). -/
  owner : ExposureId → TenantId
  /-- The resources a request on this exposure touches. -/
  touches : ExposureId → List ResourceId
  /-- The router respects the partition: every touched resource is in the
  owning tenant's scope. -/
  wf : ∀ e, ∀ res ∈ touches e, scope (owner e) res = true

/-- **Partition soundness.** Every exposure is attributed to exactly one tenant:
the binding is functional — two tenants an exposure maps to must be equal. -/
theorem owner_functional (s : System) (e : ExposureId) (t t' : TenantId)
    (h : s.owner e = t) (h' : s.owner e = t') : t = t' := by
  rw [← h, ← h']

/-- **No cross-tenant reach (the isolation invariant).** A resource touched by a
request on an exposure lies in the owning tenant's scope. -/
theorem touched_in_scope (s : System) (e : ExposureId) (res : ResourceId)
    (h : res ∈ s.touches e) : s.scope (s.owner e) res = true :=
  s.wf e res h

/-- The contrapositive: a resource outside the owning tenant's scope is never
touched. -/
theorem out_of_scope_untouched (s : System) (e : ExposureId) (res : ResourceId)
    (h : s.scope (s.owner e) res = false) : res ∉ s.touches e := by
  intro hmem
  rw [s.wf e res hmem] at h
  exact absurd h (by simp)

/-- **Disjoint tenants stay isolated.** When tenant scopes are disjoint, a
request on an exposure never touches a *different* tenant's resource. -/
theorem no_cross_tenant (s : System)
    (hdisj : ∀ t₁ t₂ res, t₁ ≠ t₂ → s.scope t₁ res = true → s.scope t₂ res = false)
    (e : ExposureId) (t : TenantId) (res : ResourceId)
    (hne : t ≠ s.owner e) (h : res ∈ s.touches e) :
    s.scope t res = false :=
  hdisj (s.owner e) t res (fun heq => hne heq.symm) (s.wf e res h)

/-! ## Capability attenuation

A capability is a resource predicate; delegation may only narrow it. -/

/-- A capability: the resources it authorizes. -/
def Cap := ResourceId → Bool

/-- `child` is an attenuation of `parent` — it authorizes no more. -/
def Sub (child parent : Cap) : Prop := ∀ res, child res = true → parent res = true

/-- Attenuation is reflexive. -/
theorem sub_refl (c : Cap) : Sub c c := fun _ h => h

/-- Attenuation is transitive: a sub-sub-exposure is within the grandparent. -/
theorem sub_trans {a b c : Cap} (hab : Sub a b) (hbc : Sub b c) : Sub a c :=
  fun res h => hbc res (hab res h)

/-- **Delegation never widens authority.** Anything a delegated (sub) capability
authorizes, the parent already authorized (grant ⊆ held). -/
theorem grant_subset_held {held grant : Cap} (h : Sub grant held)
    (res : ResourceId) (hg : grant res = true) : held res = true :=
  h res hg

/-- Adding a tenant with a fresh scope preserves pairwise disjointness, when the
new scope shares no resource with any existing one. -/
theorem disjoint_preserved
    (scope : TenantId → ResourceId → Bool) (tNew : TenantId)
    (scopeNew : ResourceId → Bool)
    (hdisj : ∀ t₁ t₂ res, t₁ ≠ t₂ → scope t₁ res = true → scope t₂ res = false)
    (hfresh : ∀ t res, scope t res = true → scopeNew res = false)
    (hfresh' : ∀ t res, scopeNew res = true → scope t res = false) :
    let scope' := fun t res => if t = tNew then scopeNew res else scope t res
    ∀ t₁ t₂ res, t₁ ≠ t₂ → scope' t₁ res = true → scope' t₂ res = false := by
  intro scope' t₁ t₂ res hne h1
  simp only [scope'] at *
  by_cases e1 : t₁ = tNew <;> by_cases e2 : t₂ = tNew
  · exact absurd (e1.trans e2.symm) hne
  · simp only [e1, if_pos] at h1
    simp only [e2, if_neg (by simpa using e2)]
    exact hfresh' t₂ res h1
  · simp only [e1, if_neg (by simpa using e1)] at h1
    simp only [e2, if_pos]
    exact hfresh t₁ res h1
  · simp only [e1, if_neg (by simpa using e1)] at h1
    simp only [e2, if_neg (by simpa using e2)]
    exact hdisj t₁ t₂ res hne h1

def version : String := "0.1.0"

end Isolation
