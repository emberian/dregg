import Dregg2.Paco.UpTo.Cpn

/-!
# GPaco with Closure (gpaco_clo)

The full gpaco definition following Coq:
  gpaco_clo clo r rg = rclo clo (paco (F ∘ rclo clo) (rg ⊔ r) ⊔ r)

## Main Definitions

- `composeRclo F clo`: Composed generating function F ∘ rclo clo
- `gpaco_clo F clo r rg`: Generalized paco with user-defined closure
- `gupaco_clo F clo r`: Symmetric version (guard = accumulator)
- `WCompatible F clo`: Weak compatibility

## Key Theorems

- `gpaco_clo_coind`: Full coinduction principle (Coq's gpacoN_cofix)
- `gpaco_clo_gupaco`: Gupaco absorption into gpaco
- `gpaco_clo_final`: GPaco is contained in gfp when clo is compatible

## References

- [Paco paper (POPL 2013)](https://plv.mpi-sws.org/paco/)
- [GPaco paper (CPP 2020)](https://paulhe.com/assets/gpaco.pdf)
- [Paco Coq: gpacoN.v](https://github.com/snu-sf/paco)
-/

namespace Paco

variable {α : Type*}

/-!
## Composed Generating Function

The key to gpaco: compose F with rclo clo to get a new monotone transformer.
-/

/-- Compose F with rclo clo to get the modified generating function.

This is `compose gf (rclo clo)` from Coq gpaco. -/
def composeRclo (F : MonoRel α) (clo : Rel α → Rel α) : MonoRel α where
  F := F ∘ rclo clo
  mono := by
    intro R S hRS
    exact F.mono' (rclo.mono hRS)

theorem composeRclo_def (F : MonoRel α) (clo : Rel α → Rel α) (R : Rel α) :
    composeRclo F clo R = F (rclo clo R) := rfl

/-!
## GPaco with Closure (gpaco_clo)
-/

/-- Generalized paco with user-defined closure operator.

`gpaco_clo F clo r rg` is the main predicate for up-to coinduction:
- `clo`: User closure operator (e.g., congruence, transitivity)
- `r`: Accumulator (immediately available facts)
- `rg`: Guard (facts available after progress)

Definition: rclo clo (paco (F ∘ rclo clo) (rg ⊔ r) ⊔ r) -/
def gpaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) : Rel α :=
  rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r)

/-- Symmetric version: guard equals accumulator -/
def gupaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r : Rel α) : Rel α :=
  gpaco_clo F clo r r

/-!
## GPaco_clo Basic Properties
-/

theorem gpaco_clo_def (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    gpaco_clo F clo r rg = rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r) := rfl

theorem gupaco_clo_def (F : MonoRel α) (clo : Rel α → Rel α) (r : Rel α) :
    gupaco_clo F clo r = gpaco_clo F clo r r := rfl

/-- r injects into gpaco_clo -/
theorem r_le_gpaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    r ≤ gpaco_clo F clo r rg := by
  intro x y hr
  exact rclo.base (Or.inr hr)

/-- paco (F ∘ rclo clo) (rg ⊔ r) injects into gpaco_clo -/
theorem paco_le_gpaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    paco (composeRclo F clo) (rg ⊔ r) ≤ gpaco_clo F clo r rg := by
  intro x y hp
  exact rclo.base (Or.inl hp)

/-- gpaco_clo is monotone in r -/
theorem gpaco_clo_mon_r (F : MonoRel α) (clo : Rel α → Rel α) (rg : Rel α)
    {r r' : Rel α} (hr : r ≤ r') : gpaco_clo F clo r rg ≤ gpaco_clo F clo r' rg := by
  unfold gpaco_clo
  apply rclo.mono
  apply sup_le_sup
  · exact paco_mon (composeRclo F clo) (sup_le_sup_left hr rg)
  · exact hr

/-- gpaco_clo is monotone in rg -/
theorem gpaco_clo_mon_rg (F : MonoRel α) (clo : Rel α → Rel α) (r : Rel α)
    {rg rg' : Rel α} (hrg : rg ≤ rg') : gpaco_clo F clo r rg ≤ gpaco_clo F clo r rg' := by
  unfold gpaco_clo
  apply rclo.mono
  apply sup_le_sup_right
  exact paco_mon (composeRclo F clo) (sup_le_sup_right hrg r)

/-- gpaco_clo is monotone in both r and rg -/
theorem gpaco_clo_mon (F : MonoRel α) (clo : Rel α → Rel α)
    {r r' rg rg' : Rel α} (hr : r ≤ r') (hrg : rg ≤ rg') :
    gpaco_clo F clo r rg ≤ gpaco_clo F clo r' rg' :=
  Rel.le_trans (gpaco_clo_mon_r F clo rg hr) (gpaco_clo_mon_rg F clo r' hrg)

/-!
## GPaco_clo Coinduction Principle

The main coinduction principle: to prove gpaco_clo F clo r rg x y,
provide a relation R with R x y such that for any rr extending rg ⊔ R,
we have R ⊆ gpaco_clo F clo r rr.
-/

/-- Helper: rclo preserves containment in gpaco_clo -/
theorem rclo_gpaco_clo_le (F : MonoRel α) (clo : Rel α → Rel α) (r rg rg' : Rel α)
    (hrg : rg ≤ rg') :
    rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r) ≤ gpaco_clo F clo r rg' := by
  unfold gpaco_clo
  apply rclo.mono
  apply sup_le_sup_right
  exact paco_mon (composeRclo F clo) (sup_le_sup_right hrg r)

/-- Full coinduction principle for gpaco_clo (Coq's gpacoN_cofix).

To prove `l ≤ gpaco_clo F clo r rg`, show that for any `rr` with
`rg ≤ rr` (INC) and `l ≤ rr` (CIH), we have `l ≤ gpaco_clo F clo r rr`.

The key insight (from Coq): First get `IN: l ≤ gpaco r (rg ⊔ l)` by instantiating
OBG with rr = rg ⊔ l. Then use coinduction to collapse `paco P ((rg ⊔ l) ⊔ r)`
back to `paco P (rg ⊔ r)`. The `l` elements get transformed via IN into the
gpaco structure, which lands in `rclo clo (W ⊔ S)` for the coinductive witness. -/
theorem gpaco_clo_coind (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α)
    (l : Rel α)
    (OBG : ∀ rr, rg ≤ rr → l ≤ rr → l ≤ gpaco_clo F clo r rr) :
    l ≤ gpaco_clo F clo r rg := by
  have IN : l ≤ gpaco_clo F clo r (rg ⊔ l) := OBG (rg ⊔ l) le_sup_left le_sup_right
  intro x y hlxy
  have hgpaco := IN x y hlxy
  simp only [gpaco_clo_def] at hgpaco ⊢
  have h_inner : paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ r ≤
                 rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r) := by
    apply sup_le
    · intro a b hpaco_ab
      apply rclo.base
      left
      apply paco_coind (composeRclo F clo) (paco (composeRclo F clo) ((rg ⊔ l) ⊔ r)) (rg ⊔ r)
      · intro u v huv
        have h_unfold := paco_unfold (composeRclo F clo) ((rg ⊔ l) ⊔ r) u v huv
        simp only [composeRclo_def] at h_unfold ⊢
        have h_rclo_le : rclo clo (upaco (composeRclo F clo) ((rg ⊔ l) ⊔ r)) ≤
                         rclo clo (paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ (rg ⊔ r)) := by
          -- Use induction on rclo structure to handle l elements that become gpaco_clo
          intro x' y' huprclo
          induction huprclo with
          | @base x' y' hbase =>
            simp only [upaco, Rel.union_apply] at hbase
            cases hbase with
            | inl hp => exact rclo.base (Or.inl hp)
            | inr hrglr =>
              cases hrglr with
              | inl hrgl =>
                cases hrgl with
                | inl hrg => exact rclo.base (Or.inr (Or.inl hrg))
                | inr hl' =>
                  -- l element: use IN to get gpaco_clo, then use rclo.mono
                  have hIN := IN x' y' hl'
                  simp only [gpaco_clo_def] at hIN
                  -- hIN : rclo clo (paco P ((rg ⊔ l) ⊔ r) ⊔ r) x' y'
                  have h_r_le : paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ r ≤
                                paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ (rg ⊔ r) :=
                    sup_le_sup_left le_sup_right _
                  exact rclo.mono h_r_le x' y' hIN
              | inr hr' => exact rclo.base (Or.inr (Or.inr hr'))
          | @clo x' y' R' hR' hcloR' ih =>
            exact rclo.clo R' ih hcloR'
        apply F.mono' h_rclo_le u v h_unfold
      · exact hpaco_ab
    · intro a b hr_ab
      exact rclo.base (Or.inr hr_ab)
  -- h_inner : paco ... ⊔ r ≤ rclo clo (paco ... ⊔ r)
  -- hgpaco : rclo clo (paco P ((rg ⊔ l) ⊔ r) ⊔ r) x y
  -- Goal: rclo clo (paco P (rg ⊔ r) ⊔ r) x y
  -- Use: rclo.mono h_inner gives rclo clo (paco ⊔ r) ≤ rclo clo (rclo clo (paco ⊔ r))
  -- Then rclo.rclo_rclo collapses the nested rclo
  exact rclo.rclo_rclo x y (rclo.mono h_inner x y hgpaco)

/-- Pointwise coinduction for gpaco_clo.

This is the pointwise version of `gpaco_clo_coind`, analogous to `paco_coind`.
It avoids needing to apply the resulting relation to `x y` manually. -/
theorem gpaco_clo_coind' (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α)
    (l : Rel α) {x y : α}
    (OBG : ∀ rr, rg ≤ rr → l ≤ rr → l ≤ gpaco_clo F clo r rr)
    (hxy : l x y) : gpaco_clo F clo r rg x y :=
  (gpaco_clo_coind F clo r rg l OBG) x y hxy

/-- Simple coinduction for gpaco_clo: prove via paco with F-progress.

To prove `gpaco_clo F clo r rg x y`, find R with R x y such that
R ⊆ F (rclo clo (R ⊔ upaco (F ∘ rclo clo) (rg ⊔ r))) ⊔ r.

Note: When R a b gives r a b (base case), no F-progress is needed. -/
theorem gpaco_clo_cofix (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α)
    (R : Rel α) {x y : α}
    (hR : R ≤ F (rclo clo (R ⊔ upaco (composeRclo F clo) (rg ⊔ r))) ⊔ r)
    (hxy : R x y) : gpaco_clo F clo r rg x y := by
  unfold gpaco_clo
  apply rclo.base
  -- Either in paco part or r part
  cases hR x y hxy with
  | inl hF =>
    -- hF : F (rclo clo (R ⊔ upaco ...)) x y - productive case
    left
    -- Define the productive subset: R elements that make F-progress
    let R' : Rel α := fun a b => R a b ∧ ∃ h : R a b, (F (rclo clo (R ⊔ upaco (composeRclo F clo) (rg ⊔ r))) a b)
    apply paco_coind (composeRclo F clo) (R' ⊔ paco (composeRclo F clo) (rg ⊔ r)) (rg ⊔ r)
    · intro a b hab
      simp only [composeRclo_def]
      cases hab with
      | inl hR'ab =>
        obtain ⟨hRab, _, hFab⟩ := hR'ab
        apply F.mono' _ a b hFab
        apply rclo.mono
        intro u v huv
        cases huv with
        | inl hRuv =>
          -- R u v - check if productive or base
          cases hR u v hRuv with
          | inl hFuv => left; left; exact ⟨hRuv, hRuv, hFuv⟩
          | inr hruv => right; right; exact hruv
        | inr hup =>
          simp only [upaco, Rel.union_apply] at hup ⊢
          cases hup with
          | inl hp => left; right; exact hp
          | inr hrg => right; exact hrg
      | inr hpaco =>
        have h := paco_unfold (composeRclo F clo) (rg ⊔ r) a b hpaco
        simp only [composeRclo_def] at h
        apply F.mono' _ a b h
        apply rclo.mono
        intro u v huv
        simp only [upaco, Rel.union_apply] at huv ⊢
        cases huv with
        | inl hp => left; right; exact hp
        | inr hrg => right; exact hrg
    · left; exact ⟨hxy, hxy, hF⟩
  | inr hr =>
    -- Base case: r x y, no coinduction needed
    right; exact hr

/-!
## Relationship to GPaco (without closure)

When clo = id, gpaco_clo reduces to something equivalent to gpaco.
-/

/-- With identity closure, composeRclo simplifies to F -/
theorem composeRclo_id (F : MonoRel α) : composeRclo F id = F := by
  cases F with
  | mk f hf =>
    simp only [composeRclo]
    congr 1
    funext R
    simp only [Function.comp_apply, rclo.rclo_id]

/-- With identity closure, gpaco_clo simplifies to gpaco -/
theorem gpaco_clo_id (F : MonoRel α) (r rg : Rel α) :
    gpaco_clo F id r rg = paco F (rg ⊔ r) ⊔ r := by
  simp only [gpaco_clo_def, rclo.rclo_id, composeRclo_id]

/-!
## Accumulation in GPaco_clo
-/

/-- gupaco_clo absorbs into gpaco_clo (requires compatible monotone closure).

This is a key accumulation lemma: facts proven via gupaco_clo can be accumulated
back into gpaco_clo, enabling compositional proofs.

Proof strategy: Direct induction on the source rclo structure.
1. For base case (paco P G): use paco_mon since G ≤ rr ⊔ r
2. For base case (G itself): use rclo.mono since G = gpaco r rg ≤ gpaco r rr (by rg ≤ rr)
3. For clo case: gpaco r rr = rclo clo (...) is closed under clo via clo_rclo -/
theorem gpaco_clo_gupaco (F : MonoRel α) (clo : Rel α → Rel α)
    (_h_mono : CloMono clo) (_h_compat : Compatible F clo)
    (r rg : Rel α) :
    gupaco_clo F clo (gpaco_clo F clo r rg) ≤ gpaco_clo F clo r rg := by
  have _ := _h_mono
  have _ := _h_compat
  let G := gpaco_clo F clo r rg
  let P := composeRclo F clo
  -- gupaco G = rclo clo (paco P (G ⊔ G) ⊔ G) = rclo clo (paco P G ⊔ G)
  -- gpaco r rg = rclo clo (paco P (rg ⊔ r) ⊔ r)
  -- Use gpaco_clo_coind to prove gupaco G ≤ gpaco r rg
  apply gpaco_clo_coind F clo r rg (gupaco_clo F clo G)
  intro rr INC CIH
  -- INC : rg ≤ rr
  -- CIH : gupaco G ≤ rr (i.e., rclo clo (paco P G ⊔ G) ≤ rr)
  -- Goal: gupaco G ≤ gpaco r rr (i.e., rclo clo (paco P G ⊔ G) ≤ rclo clo (paco P (rr ⊔ r) ⊔ r))
  -- Direct induction on source rclo structure
  simp only [gupaco_clo_def, gpaco_clo_def]
  intro x y hgup
  induction hgup with
  | @base x y hbase =>
    cases hbase with
    | inl hpaco =>
      -- hpaco : paco P G x y
      -- From CIH: paco P G ≤ gupaco G ≤ rr, so G ≤ rr (since G ≤ gupaco G)
      have h_G_le_rr : G ≤ rr := by
        intro a b hG
        have h1 : gupaco_clo F clo G a b := by
          simp only [gupaco_clo_def, gpaco_clo_def]
          exact rclo.base (Or.inr hG)
        exact CIH a b h1
      -- G ≤ rr implies G ≤ rr ⊔ r, so paco P G ≤ paco P (rr ⊔ r)
      -- (note: hpaco has type paco P (G ⊔ G) x y; G ⊔ G ≤ rr ⊔ r)
      have hG_le_rr_r : (G ⊔ G) ≤ rr ⊔ r := by
        intro a b hGG
        rcases hGG with hG | hG <;>
          exact Or.inl (h_G_le_rr a b hG)
      have hpaco' := paco_mon P hG_le_rr_r x y hpaco
      exact rclo.base (Or.inl hpaco')
    | inr hG =>
      -- hG : G x y = gpaco_clo F clo r rg x y
      -- Goal: rclo clo (paco P (rr ⊔ r) ⊔ r) x y
      -- G = rclo clo (paco P (rg ⊔ r) ⊔ r)
      -- Since rg ≤ rr (INC), we have rg ⊔ r ≤ rr ⊔ r
      -- So paco P (rg ⊔ r) ≤ paco P (rr ⊔ r) by paco_mon
      -- Thus paco P (rg ⊔ r) ⊔ r ≤ paco P (rr ⊔ r) ⊔ r
      -- And rclo clo (paco P (rg ⊔ r) ⊔ r) ≤ rclo clo (paco P (rr ⊔ r) ⊔ r) by rclo.mono
      have h_rg_r_le : rg ⊔ r ≤ rr ⊔ r := sup_le_sup_right INC r
      have h_paco_le : paco P (rg ⊔ r) ⊔ r ≤ paco P (rr ⊔ r) ⊔ r :=
        sup_le_sup_right (paco_mon P h_rg_r_le) r
      exact rclo.mono h_paco_le x y hG
  | @clo x y R' hR' hcloR' ih =>
    -- hcloR' : clo R' x y where R' ≤ rclo clo (paco P (rr ⊔ r) ⊔ r) (by ih)
    -- Goal: rclo clo (paco P (rr ⊔ r) ⊔ r) x y
    -- rclo clo X is closed under clo (by clo_rclo)
    exact rclo.clo R' ih hcloR'

/-- Key accumulation lemma: gupaco (gpaco r rg) ≤ gpaco r rg.

This is the crucial property that allows building up gpaco proofs incrementally.
When you have a gpaco predicate and use it as the accumulator for gupaco,
the result is still contained in the original gpaco.

Note: This requires `clo` to be compatible and monotone. See `gpaco_clo_gupaco` for the proof. -/
theorem gpaco_gupaco (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo)
    (r rg : Rel α) :
    gupaco_clo F clo (gpaco_clo F clo r rg) ≤ gpaco_clo F clo r rg :=
  gpaco_clo_gupaco F clo h_mono h_compat r rg

end Paco
