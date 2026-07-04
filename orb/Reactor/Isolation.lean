import Reactor.Serve
import Reactor.Bridge
import Isolation.Basic

/-!
# Reactor.Tenant — the real per-tenant Isolation partition on the deployed
dispatch

`Isolation` models per-tenant capability partition: an `Isolation.System` binds
each exposure to one owning tenant, declares the resources a request on that
exposure touches, and proves (from its `wf` field) that every touched resource
lies in the owning tenant's scope — with `no_cross_tenant` upgrading disjoint
scopes to "a request under tenant A never reaches tenant B's resources". Until
now the library was proven in isolation; no system was ever built over anything
the orb serves.

This file builds the real `Isolation.System` OVER THE DEPLOYED ROUTE TABLE —
`demoAppConfig.table`, the exact table both the test view `Reactor.serve` and the
deployed `Reactor.Deploy.serveFull` (the path `Arena.Orb.main` executes) route
against via `App.handle`:

  * an **exposure** is an index `e` into `demoAppConfig.table` — one exposure per
    deployed route (including the folded-in default);
  * a `Binding` is the operator's declaration: which tenant owns exposure `e`
    (`tenantOf`) and which resources a request on it touches (`resOf`);
  * `touchesAt` guards the declaration by the table: a non-exposure index
    touches nothing;
  * `scopeOf` GENERATES the tenant scopes from the declaration — tenant `t`
    scopes `res` iff some exposure `t` owns touches it — so the `System.wf`
    router-respects-the-partition obligation holds by construction
    (`touched_scoped`), and `systemOf` is a genuine, total `Isolation.System`
    over the deployed table for ANY binding.

**Seam theorems.**

  * `tenant_isolation_seam` (headline, test view) — when the reactor dispatches
    `req` and the test view `serve` answers with the route the real
    `Route.Match.bestMatch` chose (`serve_routes_bestMatch`), that chosen route
    IS an exposure `e` of the real tenant system (`demoAppConfig.table[e]? =
    some r`), every resource the request touches lies in the owning tenant's
    scope (the real `Isolation.touched_in_scope`), and NO other tenant's scope
    contains any of them (the real `Isolation.no_cross_tenant`, discharged with
    the demo binding's proven disjointness). A request served under tenant A
    only touches resources in the scope of tenant A.
  * `tenant_isolation_deployed` — the same partition on the DEPLOYED path
    `Arena.Orb.main` executes: hypotheses over `Reactor.Deploy.deploySubs` and
    the served bytes are `Reactor.Deploy.serveFull input` (the real header
    rewrite over the `bestMatch`-chosen route), via
    `Reactor.Deploy.deploy_routes_bestMatch` and the Bridge congruence.
  * `tenant_isolation_seam_binding` — the same positive half for an arbitrary
    operator binding, and `scopeOf_disjoint` turns any binding whose per-tenant
    resource declarations are disjoint into the `no_cross_tenant` hypothesis.
  * `request_cap_attenuates` / `exercised_within_held` — the capability a
    request actually exercises (its touched set) is an attenuation
    (`Isolation.Sub`) of the owning tenant's held capability, so
    `Isolation.grant_subset_held` applies on the serving path: exercised ⊆ held.
-/

namespace Reactor
namespace Tenant

open Proto (Bytes)

/-- The operator's tenancy declaration over the deployed route table: exposure
`e` (= table index `e`) is owned by tenant `tenantOf e` and a request on it
touches the resources `resOf e`. -/
structure Binding where
  tenantOf : Nat → Isolation.TenantId
  resOf : Nat → List Isolation.ResourceId

/-- The resources a request on exposure `e` touches: the declared set when `e`
is a real exposure (an index of the app's effective route table), nothing
otherwise. -/
def touchesAt (ac : App.AppConfig) (b : Binding) (e : Nat) :
    List Isolation.ResourceId :=
  match ac.table[e]? with
  | some _ => b.resOf e
  | none => []

/-- The generated tenant scope: tenant `t` scopes `res` iff some exposure owned
by `t` touches `res`. Generating the scope from the declaration is what makes
the partition well-formed by construction. -/
def scopeOf (ac : App.AppConfig) (b : Binding) (t : Isolation.TenantId)
    (res : Isolation.ResourceId) : Bool :=
  (List.range ac.table.length).any
    (fun i => b.tenantOf i == t && (touchesAt ac b i).any (fun x => x == res))

/-- A touched exposure is a real one: it indexes the deployed table. -/
theorem touchesAt_lt {ac : App.AppConfig} {b : Binding} {e : Nat}
    {res : Isolation.ResourceId} (h : res ∈ touchesAt ac b e) :
    e < ac.table.length := by
  rcases Nat.lt_or_ge e ac.table.length with hlt | hge
  · exact hlt
  · unfold touchesAt at h
    rw [List.getElem?_eq_none hge] at h
    exact absurd h (by simp)

/-- Characterization of the generated scope. -/
theorem scopeOf_true_iff {ac : App.AppConfig} {b : Binding}
    {t : Isolation.TenantId} {res : Isolation.ResourceId} :
    scopeOf ac b t res = true
      ↔ ∃ i, b.tenantOf i = t ∧ res ∈ touchesAt ac b i := by
  unfold scopeOf
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, _, hpred⟩
    rw [Bool.and_eq_true] at hpred
    obtain ⟨ht, hany⟩ := hpred
    rw [List.any_eq_true] at hany
    obtain ⟨x, hx, hxeq⟩ := hany
    have hxr : x = res := by exact_mod_cast beq_iff_eq.mp hxeq
    subst hxr
    exact ⟨i, beq_iff_eq.mp ht, hx⟩
  · rintro ⟨i, ht, hres⟩
    refine ⟨i, List.mem_range.mpr (touchesAt_lt hres), ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr ht, List.any_eq_true.mpr ⟨res, hres, by simp⟩⟩

/-- The `System.wf` obligation, by construction: every touched resource is in
the owning tenant's generated scope. -/
theorem touched_scoped (ac : App.AppConfig) (b : Binding) :
    ∀ e, ∀ res ∈ touchesAt ac b e, scopeOf ac b (b.tenantOf e) res = true :=
  fun e _res h => scopeOf_true_iff.mpr ⟨e, rfl, h⟩

/-- **The real `Isolation.System` over the deployed route table.** For any
operator binding, this is a total, well-formed instance of the actual
`Isolation` model whose exposures ARE the routes `serve` dispatches over. -/
def systemOf (ac : App.AppConfig) (b : Binding) : Isolation.System where
  scope := scopeOf ac b
  owner := b.tenantOf
  touches := touchesAt ac b
  wf := touched_scoped ac b

/-- Disjoint declarations generate disjoint scopes: if exposures of different
tenants never declare a common resource, then the generated tenant scopes are
pairwise disjoint — exactly the hypothesis `Isolation.no_cross_tenant` needs. -/
theorem scopeOf_disjoint (ac : App.AppConfig) (b : Binding)
    (hres : ∀ i j, b.tenantOf i ≠ b.tenantOf j →
        ∀ res, res ∈ touchesAt ac b i → res ∉ touchesAt ac b j) :
    ∀ t₁ t₂ res, t₁ ≠ t₂ →
      scopeOf ac b t₁ res = true → scopeOf ac b t₂ res = false := by
  intro t₁ t₂ res hne h1
  cases h2 : scopeOf ac b t₂ res with
  | false => rfl
  | true =>
    obtain ⟨i, hti, hri⟩ := scopeOf_true_iff.mp h1
    obtain ⟨j, htj, hrj⟩ := scopeOf_true_iff.mp h2
    exact absurd hrj (hres i j (by rw [hti, htj]; exact hne) res hri)

/-! ## The deployed instantiation -/

/-- The demo binding over the deployed table: each exposure is its own tenant,
and exposure `e` touches exactly resource `e` (three deployed exposures:
`/health`, the `/static` prefix, and the folded-in default). -/
def demoBinding : Binding where
  tenantOf := fun e => e
  resOf := fun e => [e]

/-- **THE deployed tenant system**: the real `Isolation.System` over
`demoAppConfig.table` — the table both the test view `serve` and the deployed
`Reactor.Deploy.serveFull` (`main`) route against. -/
def demoSystem : Isolation.System := systemOf demoAppConfig demoBinding

/-- In the demo binding, a resource pins its exposure: `res ∈ touchesAt e → res = e`. -/
theorem demo_touches_eq {e : Nat} {res : Isolation.ResourceId}
    (h : res ∈ touchesAt demoAppConfig demoBinding e) : res = e := by
  unfold touchesAt at h
  cases htab : demoAppConfig.table[e]? with
  | some r => rw [htab] at h; simpa [demoBinding] using h
  | none => rw [htab] at h; exact absurd h (by simp)

/-- The deployed tenant scopes are pairwise disjoint (no declared resource is
shared across tenants). -/
theorem demoBinding_disjoint :
    ∀ t₁ t₂ res, t₁ ≠ t₂ →
      demoSystem.scope t₁ res = true → demoSystem.scope t₂ res = false := by
  apply scopeOf_disjoint
  intro i j hne res hi hj
  exact absurd ((demo_touches_eq hi).symm.trans (demo_touches_eq hj)) hne

/-! ## The seam — composed with the deployed dispatch -/

/-- The positive half for ANY operator binding: the route the deployed dispatch
chose is an exposure of the real tenant system built over the deployed table,
and every resource the request touches is in the owning tenant's scope (the
real `Isolation.touched_in_scope`). -/
theorem tenant_isolation_seam_binding (b : Binding) (input : Bytes)
    (req : Proto.Request) (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest) :
    ∃ r, Route.Match.bestMatch demoAppConfig.table
            (App.targetSegments req.target) = some r
      ∧ serve input = serialize (App.responseOfHandler r.handler)
      ∧ ∃ e, demoAppConfig.table[e]? = some r
          ∧ ∀ res ∈ (systemOf demoAppConfig b).touches e,
              (systemOf demoAppConfig b).scope
                ((systemOf demoAppConfig b).owner e) res = true := by
  obtain ⟨r, hbest, hserve⟩ := serve_routes_bestMatch input req rest hsends hsub
  obtain ⟨e, he, hgetl⟩ := List.getElem_of_mem (Route.Match.bestMatch_mem hbest)
  have hget : demoAppConfig.table[e]? = some r := by
    rw [List.getElem?_eq_getElem he, hgetl]
  exact ⟨r, hbest, hserve, e, hget,
    fun res hres => Isolation.touched_in_scope (systemOf demoAppConfig b) e res hres⟩

/-- **`tenant_isolation_seam` (headline, test view).** On the test view
`Reactor.serve`: when the reactor dispatches `req` and serves the response of the
route the real `Route.Match.bestMatch` chose, that route is an exposure `e` of
the real deployed tenant system
(`demoSystem`, an `Isolation.System` over `demoAppConfig.table`), and

  * (served within scope) every resource the request touches lies in the
    OWNING tenant's scope — the real `Isolation.touched_in_scope`;
  * (no cross-tenant reach) for every OTHER tenant `t`, none of the touched
    resources is in `t`'s scope — the real `Isolation.no_cross_tenant`,
    discharged with the proven disjointness of the deployed scopes.

A request served under tenant A only touches resources in the scope of
tenant A. -/
theorem tenant_isolation_seam (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest) :
    ∃ r, Route.Match.bestMatch demoAppConfig.table
            (App.targetSegments req.target) = some r
      ∧ serve input = serialize (App.responseOfHandler r.handler)
      ∧ ∃ e, demoAppConfig.table[e]? = some r
          ∧ (∀ res ∈ demoSystem.touches e,
                demoSystem.scope (demoSystem.owner e) res = true)
          ∧ (∀ t, t ≠ demoSystem.owner e →
                ∀ res ∈ demoSystem.touches e, demoSystem.scope t res = false) := by
  obtain ⟨r, hbest, hserve, e, hget, hscope⟩ :=
    tenant_isolation_seam_binding demoBinding input req rest hsends hsub
  exact ⟨r, hbest, hserve, e, hget, hscope,
    fun t hne res hres =>
      Isolation.no_cross_tenant demoSystem demoBinding_disjoint e t res hne hres⟩

/-! ## The deployed path — the partition over `Reactor.Deploy.serveFull` -/

/-- **`tenant_isolation_deployed` — the per-tenant partition on the deployed
path.** On the path `Arena.Orb.main` executes (`Reactor.Deploy.serveFull` over
`deployConfig`): when the DEPLOYED reactor (`Reactor.Deploy.deploySubs`)
dispatches `req`, the served bytes are `serveFull input` — the REAL header
rewrite (`deployProg`: proxy/DNS upstream + `Trace` correlation id) over the
route the real `Route.Match.bestMatch` chose (`Reactor.Deploy.deploy_routes_bestMatch`)
— and that route is an exposure `e` of the real deployed tenant system
(`demoSystem`): every resource the request touches is in the OWNING tenant's
scope (`Isolation.touched_in_scope`) and NO other tenant's scope contains any of
them (`Isolation.no_cross_tenant`). The isolation content is transported from
`tenant_isolation_seam` by the Bridge congruence (`deploySubs = reactorSubs`);
the served bytes are the genuine deployed `serveFull`. -/
theorem tenant_isolation_deployed (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (Reactor.Deploy.deploySubs input) = [])
    (hsub : Reactor.Deploy.deploySubs input = .dispatch req :: rest) :
    ∃ r, Route.Match.bestMatch demoAppConfig.table
            (App.targetSegments req.target) = some r
      ∧ Reactor.Deploy.serveFull input
          = serialize (Reactor.Lifecycle.rewriteResp
              (Reactor.Deploy.deployProg
                (Reactor.Deploy.deployPlan (Reactor.Deploy.deploySubs input)) input)
              (App.responseOfHandler r.handler))
      ∧ ∃ e, demoAppConfig.table[e]? = some r
          ∧ (∀ res ∈ demoSystem.touches e,
                demoSystem.scope (demoSystem.owner e) res = true)
          ∧ (∀ t, t ≠ demoSystem.owner e →
                ∀ res ∈ demoSystem.touches e, demoSystem.scope t res = false) := by
  have hsendsR : sendsOf (reactorSubs input) = [] := by
    rw [← Reactor.Bridge.deploySubs_eq_reactorSubs]; exact hsends
  have hsubR : reactorSubs input = .dispatch req :: rest := by
    rw [← Reactor.Bridge.deploySubs_eq_reactorSubs]; exact hsub
  obtain ⟨r, hbest, _hserve, e, hget, hscope, hcross⟩ :=
    tenant_isolation_seam input req rest hsendsR hsubR
  obtain ⟨r', hbest', hserveD⟩ :=
    Reactor.Deploy.deploy_routes_bestMatch input req rest hsends hsub
  have hrr : r = r' := Option.some.inj (hbest.symm.trans hbest')
  subst hrr
  exact ⟨r, hbest, hserveD, e, hget, hscope, hcross⟩

/-! ## Attenuation on the serving path -/

/-- The capability a request on exposure `e` actually exercises: exactly its
touched resources. -/
def requestCap (s : Isolation.System) (e : Nat) : Isolation.Cap :=
  fun res => (s.touches e).any (fun x => x == res)

/-- The capability a tenant holds: its full scope. -/
def tenantCap (s : Isolation.System) (t : Isolation.TenantId) : Isolation.Cap :=
  fun res => s.scope t res

/-- The exercised capability is an attenuation (`Isolation.Sub`) of the owning
tenant's held capability — a request never exercises authority its tenant does
not hold. -/
theorem request_cap_attenuates (s : Isolation.System) (e : Nat) :
    Isolation.Sub (requestCap s e) (tenantCap s (s.owner e)) := by
  intro res h
  unfold requestCap at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hxr : x = res := by exact_mod_cast beq_iff_eq.mp hxe
  subst hxr
  exact Isolation.touched_in_scope s e x hx

/-- `Isolation.grant_subset_held`, driven on the serving path: anything the
request's capability authorizes, the owning tenant's held capability already
authorized. -/
theorem exercised_within_held (s : Isolation.System) (e : Nat)
    (res : Isolation.ResourceId) (hg : requestCap s e res = true) :
    tenantCap s (s.owner e) res = true :=
  Isolation.grant_subset_held (request_cap_attenuates s e) res hg

/-! ## Deployed sanity -/

/-- Exposure 0 of the deployed system (the `/health` route) is owned by tenant 0
and touches exactly resource 0. -/
example : demoSystem.owner 0 = 0 := rfl
example : demoSystem.touches 0 = [0] := rfl

/-- Tenant 0's scope contains its own resource… -/
example : demoSystem.scope 0 0 = true :=
  Isolation.touched_in_scope demoSystem 0 0 (by rw [show demoSystem.touches 0 = [0] from rfl]; simp)

/-- …and tenant 1 (the `/static` exposure's owner) provably cannot reach it. -/
example : demoSystem.scope 1 0 = false :=
  Isolation.no_cross_tenant demoSystem demoBinding_disjoint 0 1 0 (by decide)
    (by rw [show demoSystem.touches 0 = [0] from rfl]; simp)

end Tenant
end Reactor
