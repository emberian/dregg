/-
# Dregg2.Calculus.IntensionalCCCCategory

This file constructs the cartesian closed category presented intensionally by
`IntensionalCCCTrace`.

A shared-net morphism `A -> B` is a semantic function together with evidence
that some closed typed net represents it.  Equality forgets the chosen
representative, so this is the image/quotient of typed shared nets by exact
denotational equivalence.  `ofNet_eq_iff` proves that quotient equation in both
directions, while `ofNet_surjective` shows that no represented arrow was added
without a net.

Identity, composition, terminal maps, products, evaluation, curry, and uncurry
all carry explicit shared-net representatives.  Their universal equations are
proved as equality in a genuine `CategoryTheory.Category`.  Arrow objects use
the intensional function type from the STLC semantics; no finite function table
is materialized.

For the source language we build the parallel category of represented STLC
functions.  A proved de Bruijn renaming lemma supplies closed-term weakening.
The structural compiler induces a genuine functor, and the final law bundle
proves that it preserves the chosen terminal object, products, exponentials,
evaluation, pairing, and currying.  This is a strong-CCC result for this exact
formalized fragment.  It is not a universal embedding of arbitrary CCCs and is
not a cryptographic proof system.
-/
import Dregg2.Calculus.IntensionalCCCTrace
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

namespace Dregg2.Calculus.IntensionalCCCCategory

open CategoryTheory
open IntensionalCCCTrace

/-! ## The shared-net semantic quotient/image -/

namespace Shared

/-- Objects are exactly the types of the intensional STLC fragment. -/
structure Obj where
  ty : Ty
  deriving DecidableEq, Repr

def terminal : Obj := ⟨.unit⟩
def product (X Y : Obj) : Obj := ⟨.prod X.ty Y.ty⟩
def exponential (X Y : Obj) : Obj := ⟨.arr X.ty Y.ty⟩

/-- Closed function-valued shared nets representing arrows. -/
abbrev ClosedNet (X Y : Obj) := Net [] (.arr X.ty Y.ty)

def netSem (net : ClosedNet X Y) : Val X.ty -> Val Y.ty :=
  net.denote PUnit.unit

/-- Exact certified equivalence of two closed shared nets. -/
def CertifiedEq (left right : ClosedNet X Y) : Prop :=
  netSem left = netSem right

theorem certifiedEq_refl (net : ClosedNet X Y) : CertifiedEq net net := rfl

theorem certifiedEq_symm {left right : ClosedNet X Y}
    (h : CertifiedEq left right) : CertifiedEq right left := h.symm

theorem certifiedEq_trans {left middle right : ClosedNet X Y}
    (h₁ : CertifiedEq left middle) (h₂ : CertifiedEq middle right) :
    CertifiedEq left right := h₁.trans h₂

/-- A semantic arrow with a typed shared-net representative.  Representative
existence is proof data, so arrow equality is exactly function equality. -/
structure Hom (X Y : Obj) where
  toFun : Val X.ty -> Val Y.ty
  represented : ∃ net : ClosedNet X Y, netSem net = toFun

instance (X Y : Obj) : CoeFun (Hom X Y) (fun _ => Val X.ty -> Val Y.ty) :=
  ⟨Hom.toFun⟩

@[ext]
theorem Hom.ext {X Y : Obj} {f g : Hom X Y} (h : f.toFun = g.toFun) : f = g := by
  cases f with
  | mk ff hf =>
    cases g with
    | mk gg hg =>
      cases h
      rfl

theorem Hom.eq_iff {X Y : Obj} {f g : Hom X Y} :
    f = g ↔ f.toFun = g.toFun := by
  exact ⟨congrArg Hom.toFun, Hom.ext⟩

/-- Send a concrete typed net to its semantic equivalence class. -/
def ofNet (net : ClosedNet X Y) : Hom X Y where
  toFun := netSem net
  represented := ⟨net, rfl⟩

/-- Quotient exactness: concrete nets yield equal arrows exactly when they are
certifiably denotationally equivalent. -/
theorem ofNet_eq_iff (left right : ClosedNet X Y) :
    ofNet left = ofNet right ↔ CertifiedEq left right := by
  rw [Hom.eq_iff]
  rfl

/-- Every arrow in the category has a concrete closed shared-net
representative. -/
theorem ofNet_surjective : Function.Surjective (ofNet : ClosedNet X Y -> Hom X Y) := by
  intro f
  rcases f.represented with ⟨net, hnet⟩
  refine ⟨net, Hom.ext ?_⟩
  exact hnet

/-! ### Explicit representatives for the categorical operations -/

def idNet (X : Obj) : ClosedNet X X := .lam (.var .zero)

/-- First `f`, then `g`; both closed functions are lifted beneath the input
binder without copying or tabulating them. -/
def compNet (f : ClosedNet X Y) (g : ClosedNet Y Z) : ClosedNet X Z :=
  .lam (.app (.lift g) (.app (.lift f) (.var .zero)))

@[simp] theorem netSem_idNet (X : Obj) : netSem (idNet X) = id := rfl

@[simp] theorem netSem_compNet (f : ClosedNet X Y) (g : ClosedNet Y Z) :
    netSem (compNet f g) = fun x => netSem g (netSem f x) := rfl

def idHom (X : Obj) : Hom X X := ofNet (idNet X)

def compHom {X Y Z : Obj} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toFun := fun x => g.toFun (f.toFun x)
  represented := by
    rcases f.represented with ⟨fn, hfn⟩
    rcases g.represented with ⟨gn, hgn⟩
    refine ⟨compNet fn gn, ?_⟩
    funext x
    change netSem gn (netSem fn x) = g.toFun (f.toFun x)
    rw [congrFun hfn x, congrFun hgn (f.toFun x)]

/-- The semantic quotient/image is a genuine category. -/
instance categoryShared : Category Obj where
  Hom := Hom
  id := idHom
  comp := compHom
  id_comp := by intros; apply Hom.ext; rfl
  comp_id := by intros; apply Hom.ext; rfl
  assoc := by intros; apply Hom.ext; rfl

@[simp] theorem id_apply (X : Obj) (x : Val X.ty) :
    (𝟙 X : X ⟶ X).toFun x = x := rfl

@[simp] theorem comp_apply {X Y Z : Obj} (f : Hom X Y) (g : Hom Y Z)
    (x : Val X.ty) : (compHom f g).toFun x = g.toFun (f.toFun x) := rfl

/-- A certified local rewrite between closed arrows is equality in the
category. -/
theorem localStep_certifiedEq {before after : ClosedNet X Y}
    (step : LocalStep before after) : CertifiedEq before after := by
  funext x
  exact congrFun (localStep_denote step PUnit.unit).symm x

theorem ofNet_localStep_eq {before after : ClosedNet X Y}
    (step : LocalStep before after) : ofNet before = ofNet after :=
  (ofNet_eq_iff before after).mpr (localStep_certifiedEq step)

theorem trace_certifiedEq {before after : ClosedNet X Y}
    (trace : Trace before after) : CertifiedEq before after := by
  funext x
  exact congrFun (trace_denote trace PUnit.unit).symm x

theorem ofNet_trace_eq {before after : ClosedNet X Y}
    (trace : Trace before after) : ofNet before = ofNet after :=
  (ofNet_eq_iff before after).mpr (trace_certifiedEq trace)

/-! ### Terminal object and products -/

def terminateNet (X : Obj) : ClosedNet X terminal := .lam .unit

def fstNet (X Y : Obj) : ClosedNet (product X Y) X := .lam (.fst (.var .zero))
def sndNet (X Y : Obj) : ClosedNet (product X Y) Y := .lam (.snd (.var .zero))

def pairNet (f : ClosedNet Z X) (g : ClosedNet Z Y) :
    ClosedNet Z (product X Y) :=
  .lam (.pair (.app (.lift f) (.var .zero))
    (.app (.lift g) (.var .zero)))

@[simp] theorem netSem_terminateNet (X : Obj) :
    netSem (terminateNet X) = fun _ => PUnit.unit := rfl

@[simp] theorem netSem_fstNet (X Y : Obj) :
    netSem (fstNet X Y) = Prod.fst := rfl

@[simp] theorem netSem_sndNet (X Y : Obj) :
    netSem (sndNet X Y) = Prod.snd := rfl

@[simp] theorem netSem_pairNet (f : ClosedNet Z X) (g : ClosedNet Z Y) :
    netSem (pairNet f g) = fun z => (netSem f z, netSem g z) := rfl

def toTerminal (X : Obj) : X ⟶ terminal := ofNet (terminateNet X)
def fst (X Y : Obj) : product X Y ⟶ X := ofNet (fstNet X Y)
def snd (X Y : Obj) : product X Y ⟶ Y := ofNet (sndNet X Y)

def pair {Z X Y : Obj} (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ product X Y where
  toFun := fun z => (f.toFun z, g.toFun z)
  represented := by
    rcases f.represented with ⟨fn, hfn⟩
    rcases g.represented with ⟨gn, hgn⟩
    refine ⟨pairNet fn gn, ?_⟩
    funext z
    change (netSem fn z, netSem gn z) = (f.toFun z, g.toFun z)
    rw [congrFun hfn z, congrFun hgn z]

theorem toTerminal_unique (f : X ⟶ terminal) : f = toTerminal X := by
  apply Hom.ext
  funext x
  exact PUnit.ext _ _

@[simp] theorem fst_pair (f : Z ⟶ X) (g : Z ⟶ Y) :
    pair f g ≫ fst X Y = f := by apply Hom.ext; rfl

@[simp] theorem snd_pair (f : Z ⟶ X) (g : Z ⟶ Y) :
    pair f g ≫ snd X Y = g := by apply Hom.ext; rfl

@[simp] theorem pair_fst_snd (h : Z ⟶ product X Y) :
    pair (h ≫ fst X Y) (h ≫ snd X Y) = h := by
  apply Hom.ext
  funext z
  exact Prod.eta _

theorem pair_unique (h : Z ⟶ product X Y) (f : Z ⟶ X) (g : Z ⟶ Y)
    (hfst : h ≫ fst X Y = f) (hsnd : h ≫ snd X Y = g) :
    h = pair f g := by
  rw [← hfst, ← hsnd, pair_fst_snd]

/-! ### Exponentials -/

def evaluationNet (X Y : Obj) : ClosedNet (product (exponential X Y) X) Y :=
  .lam (.app (.fst (.var .zero)) (.snd (.var .zero)))

def curryNet (f : ClosedNet (product Z X) Y) : ClosedNet Z (exponential X Y) :=
  .lam (.lam (.app (.lift (.lift f))
    (.pair (.var (.succ .zero)) (.var .zero))))

def uncurryNet (g : ClosedNet Z (exponential X Y)) :
    ClosedNet (product Z X) Y :=
  .lam (.app (.app (.lift g) (.fst (.var .zero))) (.snd (.var .zero)))

@[simp] theorem netSem_evaluationNet (X Y : Obj) :
    netSem (evaluationNet X Y) = fun fx => fx.1 fx.2 := rfl

@[simp] theorem netSem_curryNet (f : ClosedNet (product Z X) Y) :
    netSem (curryNet f) = fun z x => netSem f (z, x) := rfl

@[simp] theorem netSem_uncurryNet (g : ClosedNet Z (exponential X Y)) :
    netSem (uncurryNet g) = fun zx => netSem g zx.1 zx.2 := rfl

def evaluation (X Y : Obj) : product (exponential X Y) X ⟶ Y :=
  ofNet (evaluationNet X Y)

def curry {Z X Y : Obj} (f : product Z X ⟶ Y) : Z ⟶ exponential X Y where
  toFun := fun z x => f.toFun (z, x)
  represented := by
    rcases f.represented with ⟨fn, hfn⟩
    refine ⟨curryNet fn, ?_⟩
    funext z x
    change netSem fn (z, x) = f.toFun (z, x)
    exact congrFun hfn (z, x)

def uncurry {Z X Y : Obj} (g : Z ⟶ exponential X Y) : product Z X ⟶ Y where
  toFun := fun zx => g.toFun zx.1 zx.2
  represented := by
    rcases g.represented with ⟨gn, hgn⟩
    refine ⟨uncurryNet gn, ?_⟩
    funext zx
    change netSem gn zx.1 zx.2 = g.toFun zx.1 zx.2
    rw [congrFun hgn zx.1]

@[simp] theorem uncurry_curry (f : product Z X ⟶ Y) :
    uncurry (curry f) = f := by apply Hom.ext; rfl

@[simp] theorem curry_uncurry (g : Z ⟶ exponential X Y) :
    curry (uncurry g) = g := by apply Hom.ext; rfl

theorem uncurry_eq_evaluation (g : Z ⟶ exponential X Y) :
    uncurry g = pair (fst Z X ≫ g) (snd Z X) ≫ evaluation X Y := by
  apply Hom.ext
  rfl

theorem evaluation_beta (f : product Z X ⟶ Y) :
    pair (fst Z X ≫ curry f) (snd Z X) ≫ evaluation X Y = f := by
  rw [← uncurry_eq_evaluation, uncurry_curry]

theorem curry_unique (f : product Z X ⟶ Y) (g : Z ⟶ exponential X Y)
    (heval : pair (fst Z X ≫ g) (snd Z X) ≫ evaluation X Y = f) :
    g = curry f := by
  rw [← uncurry_eq_evaluation] at heval
  rw [← heval, curry_uncurry]

/-- Complete chosen CCC law package for the genuine shared-net category. -/
structure Laws : Prop where
  terminality : ∀ {X} (f : X ⟶ terminal), f = toTerminal X
  productBetaFst : ∀ {Z X Y} (f : Z ⟶ X) (g : Z ⟶ Y), pair f g ≫ fst X Y = f
  productBetaSnd : ∀ {Z X Y} (f : Z ⟶ X) (g : Z ⟶ Y), pair f g ≫ snd X Y = g
  productEta : ∀ {Z X Y} (h : Z ⟶ product X Y),
    pair (h ≫ fst X Y) (h ≫ snd X Y) = h
  exponentialBeta : ∀ {Z X Y} (f : product Z X ⟶ Y), uncurry (curry f) = f
  exponentialEta : ∀ {Z X Y} (g : Z ⟶ exponential X Y), curry (uncurry g) = g

theorem laws : Laws where
  terminality := toTerminal_unique
  productBetaFst := fst_pair
  productBetaSnd := snd_pair
  productEta := pair_fst_snd
  exponentialBeta := uncurry_curry
  exponentialEta := curry_uncurry

end Shared

/-! ## Source renaming and the source STLC category -/

namespace Syntax

abbrev Ren (Γ Δ : List Ty) := ∀ {A}, Var Γ A -> Var Δ A

def Ren.lift (ρ : Ren Γ Δ) : Ren (B :: Γ) (B :: Δ)
  | _, .zero => .zero
  | _, .succ x => .succ (ρ x)

def rename (ρ : Ren Γ Δ) : Tm Γ A -> Tm Δ A
  | .var x => .var (ρ x)
  | .unit => .unit
  | .lit n => .lit n
  | .succ n => .succ (rename ρ n)
  | .pair left right => .pair (rename ρ left) (rename ρ right)
  | .fst p => .fst (rename ρ p)
  | .snd p => .snd (rename ρ p)
  | .lam body => .lam (rename ρ.lift body)
  | .app fn arg => .app (rename ρ fn) (rename ρ arg)
  | .let1 value body => .let1 (rename ρ value) (rename ρ.lift body)

/-- Pull a target environment back along a variable renaming. -/
def Env.pull : {Γ Δ : List Ty} -> Ren Γ Δ -> Env Δ -> Env Γ
  | [], _, _, _ => PUnit.unit
  | _ :: _, _, ρ, env =>
      (lookup (ρ .zero) env, Env.pull (fun x => ρ (.succ x)) env)

theorem lookup_pull (ρ : Ren Γ Δ) (x : Var Γ A) (env : Env Δ) :
    lookup x (Env.pull ρ env) = lookup (ρ x) env := by
  induction x with
  | zero => rfl
  | succ x ih => exact ih (fun y => ρ (.succ y))

theorem pull_weaken (ρ : Ren Γ Δ) (x : Val B) (env : Env Δ) :
    Env.pull (fun {A} (v : Var Γ A) => Var.succ (ρ v)) (x, env) = Env.pull ρ env := by
  induction Γ with
  | nil => rfl
  | cons C Γ ih =>
      apply Prod.ext
      · rfl
      · exact ih (fun {A} (v : Var Γ A) => ρ (.succ v))

theorem pull_lift (ρ : Ren Γ Δ) (x : Val B) (env : Env Δ) :
    Env.pull ρ.lift (x, env) = (x, Env.pull ρ env) := by
  apply Prod.ext
  · rfl
  · exact pull_weaken ρ x env

theorem denote_rename (term : Tm Γ A) :
    ∀ {Δ : List Ty} (ρ : Ren Γ Δ) (env : Env Δ),
      (rename ρ term).denote env = term.denote (Env.pull ρ env) := by
  induction term with
  | var v =>
      intro Δ ρ env
      exact (lookup_pull ρ v env).symm
  | unit => intros; rfl
  | lit => intros; rfl
  | succ n ih =>
      intro Δ ρ env
      simp [rename, Tm.denote, ih]
  | pair left right ihl ihr =>
      intro Δ ρ env
      simp [rename, Tm.denote, ihl, ihr]
  | fst p ih =>
      intro Δ ρ env
      simp [rename, Tm.denote, ih]
  | snd p ih =>
      intro Δ ρ env
      simp [rename, Tm.denote, ih]
  | lam body ih =>
      intro Δ ρ env
      simp only [rename, Tm.denote]
      funext x
      rw [ih ρ.lift (x, env), pull_lift]
  | app fn arg ihf iha =>
      intro Δ ρ env
      simp [rename, Tm.denote, ihf, iha]
  | let1 value body ihv ihb =>
      intro Δ ρ env
      simp only [rename, Tm.denote, ihv ρ env]
      rw [ihb ρ.lift (_, env), pull_lift]

/-- Unique renaming from the empty context. -/
def emptyRen (Γ : List Ty) : Ren [] Γ := fun x => nomatch x

def closedLift (term : Tm [] A) (Γ : List Ty) : Tm Γ A :=
  rename (emptyRen Γ) term

@[simp] theorem denote_closedLift (term : Tm [] A) (env : Env Γ) :
    (closedLift term Γ).denote env = term.denote PUnit.unit := by
  rw [closedLift, denote_rename]
  rfl

/-- Source objects are kept distinct from shared-net objects so both genuine
category instances coexist. -/
structure Obj where
  ty : Ty
  deriving DecidableEq, Repr

def terminal : Obj := ⟨.unit⟩
def product (X Y : Obj) : Obj := ⟨.prod X.ty Y.ty⟩
def exponential (X Y : Obj) : Obj := ⟨.arr X.ty Y.ty⟩

abbrev ClosedTm (X Y : Obj) := Tm [] (.arr X.ty Y.ty)

def termSem (term : ClosedTm X Y) : Val X.ty -> Val Y.ty :=
  term.denote PUnit.unit

structure Hom (X Y : Obj) where
  toFun : Val X.ty -> Val Y.ty
  represented : ∃ term : ClosedTm X Y, termSem term = toFun

instance (X Y : Obj) : CoeFun (Hom X Y) (fun _ => Val X.ty -> Val Y.ty) :=
  ⟨Hom.toFun⟩

@[ext] theorem Hom.ext {X Y : Obj} {f g : Hom X Y}
    (h : f.toFun = g.toFun) : f = g := by
  cases f with
  | mk ff hf =>
    cases g with
    | mk gg hg =>
      cases h
      rfl

def ofTerm (term : ClosedTm X Y) : Hom X Y where
  toFun := termSem term
  represented := ⟨term, rfl⟩

def idTerm (X : Obj) : ClosedTm X X := .lam (.var .zero)

def compTerm (f : ClosedTm X Y) (g : ClosedTm Y Z) : ClosedTm X Z :=
  .lam (.app (closedLift g [X.ty])
    (.app (closedLift f [X.ty]) (.var .zero)))

@[simp] theorem termSem_compTerm (f : ClosedTm X Y) (g : ClosedTm Y Z) :
    termSem (compTerm f g) = fun x => termSem g (termSem f x) := by
  funext x
  simp [termSem, compTerm, Tm.denote, lookup,
    denote_closedLift (Γ := [X.ty]) (env := (x, PUnit.unit))]

def idHom (X : Obj) : Hom X X := ofTerm (idTerm X)

def compHom {X Y Z : Obj} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toFun := fun x => g.toFun (f.toFun x)
  represented := by
    rcases f.represented with ⟨ft, hft⟩
    rcases g.represented with ⟨gt, hgt⟩
    refine ⟨compTerm ft gt, ?_⟩
    rw [termSem_compTerm]
    funext x
    change termSem gt (termSem ft x) = g.toFun (f.toFun x)
    rw [congrFun hft x, congrFun hgt (f.toFun x)]

instance categorySyntax : Category Obj where
  Hom := Hom
  id := idHom
  comp := compHom
  id_comp := by intros; apply Hom.ext; rfl
  comp_id := by intros; apply Hom.ext; rfl
  assoc := by intros; apply Hom.ext; rfl

def terminateTerm (X : Obj) : ClosedTm X terminal := .lam .unit
def fstTerm (X Y : Obj) : ClosedTm (product X Y) X := .lam (.fst (.var .zero))
def sndTerm (X Y : Obj) : ClosedTm (product X Y) Y := .lam (.snd (.var .zero))

def pairTerm (f : ClosedTm Z X) (g : ClosedTm Z Y) : ClosedTm Z (product X Y) :=
  .lam (.pair (.app (closedLift f [Z.ty]) (.var .zero))
    (.app (closedLift g [Z.ty]) (.var .zero)))

def evaluationTerm (X Y : Obj) : ClosedTm (product (exponential X Y) X) Y :=
  .lam (.app (.fst (.var .zero)) (.snd (.var .zero)))

def curryTerm (f : ClosedTm (product Z X) Y) : ClosedTm Z (exponential X Y) :=
  .lam (.lam (.app (closedLift f [X.ty, Z.ty])
    (.pair (.var (.succ .zero)) (.var .zero))))

def uncurryTerm (g : ClosedTm Z (exponential X Y)) : ClosedTm (product Z X) Y :=
  .lam (.app (.app (closedLift g [Ty.prod Z.ty X.ty]) (.fst (.var .zero)))
    (.snd (.var .zero)))

@[simp] theorem termSem_pairTerm (f : ClosedTm Z X) (g : ClosedTm Z Y) :
    termSem (pairTerm f g) = fun z => (termSem f z, termSem g z) := by
  funext z
  simp [termSem, pairTerm, Tm.denote, lookup,
    denote_closedLift (Γ := [Z.ty]) (env := (z, PUnit.unit))]
  rfl

@[simp] theorem termSem_curryTerm (f : ClosedTm (product Z X) Y) :
    termSem (curryTerm f) = fun z x => termSem f (z, x) := by
  funext z x
  simp [termSem, curryTerm, Tm.denote, lookup,
    denote_closedLift (Γ := [X.ty, Z.ty]) (env := (x, z, PUnit.unit))]

@[simp] theorem termSem_uncurryTerm (g : ClosedTm Z (exponential X Y)) :
    termSem (uncurryTerm g) = fun zx => termSem g zx.1 zx.2 := by
  funext zx
  simp only [termSem, uncurryTerm, Tm.denote, lookup]
  exact congrFun (congrFun
    (denote_closedLift (Γ := [Ty.prod Z.ty X.ty]) g (zx, PUnit.unit)) zx.1) zx.2

def toTerminal (X : Obj) : X ⟶ terminal := ofTerm (terminateTerm X)
def fst (X Y : Obj) : product X Y ⟶ X := ofTerm (fstTerm X Y)
def snd (X Y : Obj) : product X Y ⟶ Y := ofTerm (sndTerm X Y)
def evaluation (X Y : Obj) : product (exponential X Y) X ⟶ Y :=
  ofTerm (evaluationTerm X Y)

def pair {Z X Y : Obj} (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ product X Y where
  toFun := fun z => (f.toFun z, g.toFun z)
  represented := by
    rcases f.represented with ⟨ft, hft⟩
    rcases g.represented with ⟨gt, hgt⟩
    refine ⟨pairTerm ft gt, ?_⟩
    rw [termSem_pairTerm]
    funext z
    change (termSem ft z, termSem gt z) = (f.toFun z, g.toFun z)
    rw [congrFun hft z, congrFun hgt z]

def curry {Z X Y : Obj} (f : product Z X ⟶ Y) : Z ⟶ exponential X Y where
  toFun := fun z x => f.toFun (z, x)
  represented := by
    rcases f.represented with ⟨ft, hft⟩
    refine ⟨curryTerm ft, ?_⟩
    rw [termSem_curryTerm]
    funext z x
    change termSem ft (z, x) = f.toFun (z, x)
    exact congrFun hft (z, x)

def uncurry {Z X Y : Obj} (g : Z ⟶ exponential X Y) : product Z X ⟶ Y where
  toFun := fun zx => g.toFun zx.1 zx.2
  represented := by
    rcases g.represented with ⟨gt, hgt⟩
    refine ⟨uncurryTerm gt, ?_⟩
    rw [termSem_uncurryTerm]
    funext zx
    change termSem gt zx.1 zx.2 = g.toFun zx.1 zx.2
    rw [congrFun hgt zx.1]

theorem toTerminal_unique (f : X ⟶ terminal) : f = toTerminal X := by
  apply Hom.ext
  funext x
  exact PUnit.ext _ _

@[simp] theorem fst_pair (f : Z ⟶ X) (g : Z ⟶ Y) :
    pair f g ≫ fst X Y = f := by apply Hom.ext; rfl

@[simp] theorem snd_pair (f : Z ⟶ X) (g : Z ⟶ Y) :
    pair f g ≫ snd X Y = g := by apply Hom.ext; rfl

@[simp] theorem pair_fst_snd (h : Z ⟶ product X Y) :
    pair (h ≫ fst X Y) (h ≫ snd X Y) = h := by
  apply Hom.ext
  funext z
  exact Prod.eta _

@[simp] theorem uncurry_curry (f : product Z X ⟶ Y) :
    uncurry (curry f) = f := by apply Hom.ext; rfl

@[simp] theorem curry_uncurry (g : Z ⟶ exponential X Y) :
    curry (uncurry g) = g := by apply Hom.ext; rfl

/-- The source quotient/image is itself a CCC; these are the exact chosen
operations subsequently preserved by the compiler. -/
structure Laws : Prop where
  terminality : ∀ {X} (f : X ⟶ terminal), f = toTerminal X
  productBetaFst : ∀ {Z X Y} (f : Z ⟶ X) (g : Z ⟶ Y), pair f g ≫ fst X Y = f
  productBetaSnd : ∀ {Z X Y} (f : Z ⟶ X) (g : Z ⟶ Y), pair f g ≫ snd X Y = g
  productEta : ∀ {Z X Y} (h : Z ⟶ product X Y),
    pair (h ≫ fst X Y) (h ≫ snd X Y) = h
  exponentialBeta : ∀ {Z X Y} (f : product Z X ⟶ Y), uncurry (curry f) = f
  exponentialEta : ∀ {Z X Y} (g : Z ⟶ exponential X Y), curry (uncurry g) = g

theorem laws : Laws where
  terminality := toTerminal_unique
  productBetaFst := fst_pair
  productBetaSnd := snd_pair
  productEta := pair_fst_snd
  exponentialBeta := uncurry_curry
  exponentialEta := curry_uncurry

end Syntax

/-! ## The structural compiler as a strong CCC functor -/

namespace Compiler

def obj (X : Syntax.Obj) : Shared.Obj := ⟨X.ty⟩

def mapHom {X Y : Syntax.Obj} (f : Syntax.Hom X Y) :
    Shared.Hom (obj X) (obj Y) where
  toFun := f.toFun
  represented := by
    rcases f.represented with ⟨term, hterm⟩
    refine ⟨compile term, ?_⟩
    funext x
    exact (congrFun (compile_denote term PUnit.unit) x).trans (congrFun hterm x)

def compilerFunctor : CategoryTheory.Functor Syntax.Obj Shared.Obj where
  obj := obj
  map := mapHom
  map_id := by intro X; apply Shared.Hom.ext; rfl
  map_comp := by intro X Y Z f g; apply Shared.Hom.ext; rfl

/-- On a concrete source representative, the functor is exactly the structural
compiler modulo the proved shared-net equivalence. -/
theorem map_ofTerm_eq_ofNet (term : Syntax.ClosedTm X Y) :
    compilerFunctor.map (Syntax.ofTerm term) = Shared.ofNet (compile term) := by
  apply Shared.Hom.ext
  funext x
  exact congrFun (compile_denote term PUnit.unit).symm x

theorem maps_identity (X : Syntax.Obj) :
    compilerFunctor.map (𝟙 X) = 𝟙 (compilerFunctor.obj X) :=
  compilerFunctor.map_id X

theorem maps_composition (f : X ⟶ Y) (g : Y ⟶ Z) :
    compilerFunctor.map (f ≫ g) = compilerFunctor.map f ≫ compilerFunctor.map g :=
  compilerFunctor.map_comp f g

theorem maps_terminal : compilerFunctor.obj Syntax.terminal = Shared.terminal := rfl

theorem maps_product (X Y : Syntax.Obj) :
    compilerFunctor.obj (Syntax.product X Y) =
      Shared.product (compilerFunctor.obj X) (compilerFunctor.obj Y) := rfl

theorem maps_exponential (X Y : Syntax.Obj) :
    compilerFunctor.obj (Syntax.exponential X Y) =
      Shared.exponential (compilerFunctor.obj X) (compilerFunctor.obj Y) := rfl

theorem maps_toTerminal (X : Syntax.Obj) :
    compilerFunctor.map (Syntax.toTerminal X) =
      Shared.toTerminal (compilerFunctor.obj X) := by
  apply Shared.Hom.ext
  rfl

theorem maps_fst (X Y : Syntax.Obj) :
    compilerFunctor.map (Syntax.fst X Y) =
      Shared.fst (compilerFunctor.obj X) (compilerFunctor.obj Y) := by
  apply Shared.Hom.ext
  rfl

theorem maps_snd (X Y : Syntax.Obj) :
    compilerFunctor.map (Syntax.snd X Y) =
      Shared.snd (compilerFunctor.obj X) (compilerFunctor.obj Y) := by
  apply Shared.Hom.ext
  rfl

theorem maps_pair {Z X Y : Syntax.Obj} (f : Z ⟶ X) (g : Z ⟶ Y) :
    compilerFunctor.map (Syntax.pair f g) =
      Shared.pair (compilerFunctor.map f) (compilerFunctor.map g) := by
  apply Shared.Hom.ext
  rfl

theorem maps_evaluation (X Y : Syntax.Obj) :
    compilerFunctor.map (Syntax.evaluation X Y) =
      Shared.evaluation (compilerFunctor.obj X) (compilerFunctor.obj Y) := by
  apply Shared.Hom.ext
  rfl

theorem maps_curry {Z X Y : Syntax.Obj} (f : Syntax.product Z X ⟶ Y) :
    compilerFunctor.map (Syntax.curry f) =
      Shared.curry (Z := obj Z) (X := obj X) (Y := obj Y) (compilerFunctor.map f) := by
  apply Shared.Hom.ext
  rfl

theorem maps_uncurry {Z X Y : Syntax.Obj} (g : Z ⟶ Syntax.exponential X Y) :
    compilerFunctor.map (Syntax.uncurry g) =
      Shared.uncurry (Z := obj Z) (X := obj X) (Y := obj Y) (compilerFunctor.map g) := by
  apply Shared.Hom.ext
  rfl

/-- Strong preservation of the chosen CCC structure. -/
structure StrongCCCPreservation : Prop where
  terminalObject : compilerFunctor.obj Syntax.terminal = Shared.terminal
  productObject : ∀ X Y, compilerFunctor.obj (Syntax.product X Y) =
    Shared.product (compilerFunctor.obj X) (compilerFunctor.obj Y)
  exponentialObject : ∀ X Y, compilerFunctor.obj (Syntax.exponential X Y) =
    Shared.exponential (compilerFunctor.obj X) (compilerFunctor.obj Y)
  terminalArrow : ∀ X, compilerFunctor.map (Syntax.toTerminal X) =
    Shared.toTerminal (compilerFunctor.obj X)
  firstProjection : ∀ X Y, compilerFunctor.map (Syntax.fst X Y) =
    Shared.fst (compilerFunctor.obj X) (compilerFunctor.obj Y)
  secondProjection : ∀ X Y, compilerFunctor.map (Syntax.snd X Y) =
    Shared.snd (compilerFunctor.obj X) (compilerFunctor.obj Y)
  pairing : ∀ {Z X Y : Syntax.Obj} (f : Z ⟶ X) (g : Z ⟶ Y),
    compilerFunctor.map (Syntax.pair f g) =
      Shared.pair (compilerFunctor.map f) (compilerFunctor.map g)
  evaluation : ∀ X Y, compilerFunctor.map (Syntax.evaluation X Y) =
    Shared.evaluation (compilerFunctor.obj X) (compilerFunctor.obj Y)
  currying : ∀ {Z X Y : Syntax.Obj} (f : Syntax.product Z X ⟶ Y),
    compilerFunctor.map (Syntax.curry f) =
      Shared.curry (Z := obj Z) (X := obj X) (Y := obj Y) (compilerFunctor.map f)
  uncurrying : ∀ {Z X Y : Syntax.Obj} (g : Z ⟶ Syntax.exponential X Y),
    compilerFunctor.map (Syntax.uncurry g) =
      Shared.uncurry (Z := obj Z) (X := obj X) (Y := obj Y) (compilerFunctor.map g)

theorem strongCCC : StrongCCCPreservation where
  terminalObject := maps_terminal
  productObject := maps_product
  exponentialObject := maps_exponential
  terminalArrow := maps_toTerminal
  firstProjection := maps_fst
  secondProjection := maps_snd
  pairing := maps_pair
  evaluation := maps_evaluation
  currying := maps_curry
  uncurrying := maps_uncurry

end Compiler

#assert_all_clean [
  Shared.certifiedEq_refl,
  Shared.certifiedEq_symm,
  Shared.certifiedEq_trans,
  Shared.Hom.eq_iff,
  Shared.ofNet_eq_iff,
  Shared.ofNet_surjective,
  Shared.netSem_idNet,
  Shared.netSem_compNet,
  Shared.id_apply,
  Shared.comp_apply,
  Shared.localStep_certifiedEq,
  Shared.ofNet_localStep_eq,
  Shared.trace_certifiedEq,
  Shared.ofNet_trace_eq,
  Shared.netSem_terminateNet,
  Shared.netSem_fstNet,
  Shared.netSem_sndNet,
  Shared.netSem_pairNet,
  Shared.toTerminal_unique,
  Shared.fst_pair,
  Shared.snd_pair,
  Shared.pair_fst_snd,
  Shared.pair_unique,
  Shared.netSem_evaluationNet,
  Shared.netSem_curryNet,
  Shared.netSem_uncurryNet,
  Shared.uncurry_curry,
  Shared.curry_uncurry,
  Shared.uncurry_eq_evaluation,
  Shared.evaluation_beta,
  Shared.curry_unique,
  Shared.laws,
  Syntax.lookup_pull,
  Syntax.pull_weaken,
  Syntax.pull_lift,
  Syntax.denote_rename,
  Syntax.denote_closedLift,
  Syntax.termSem_compTerm,
  Syntax.termSem_pairTerm,
  Syntax.termSem_curryTerm,
  Syntax.termSem_uncurryTerm,
  Syntax.toTerminal_unique,
  Syntax.fst_pair,
  Syntax.snd_pair,
  Syntax.pair_fst_snd,
  Syntax.uncurry_curry,
  Syntax.curry_uncurry,
  Syntax.laws,
  Compiler.map_ofTerm_eq_ofNet,
  Compiler.maps_identity,
  Compiler.maps_composition,
  Compiler.maps_terminal,
  Compiler.maps_product,
  Compiler.maps_exponential,
  Compiler.maps_toTerminal,
  Compiler.maps_fst,
  Compiler.maps_snd,
  Compiler.maps_pair,
  Compiler.maps_evaluation,
  Compiler.maps_curry,
  Compiler.maps_uncurry,
  Compiler.strongCCC
]

end Dregg2.Calculus.IntensionalCCCCategory
