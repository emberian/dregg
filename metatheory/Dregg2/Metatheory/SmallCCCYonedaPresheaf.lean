/-
# Small cartesian closed categories embed strongly in presheaves

For a genuinely small cartesian closed category `C`, the Yoneda embedding

    C ⟶ (Cᵒᵖ ⟶ Type)

is fully faithful, preserves terminal objects and binary products, and sends
the chosen exponential `B^A` to the presheaf exponential between `y A` and
`y B`.

This statement has no finiteness hypothesis.  In particular, it is a semantic
embedding into the (generally infinite) presheaf topos; this module uses and
formalizes its cartesian closed structure.  It is not a finite-field encoding,
a bounded-coordinate presentation, or a succinct arithmetization.
The finite-field size and cost questions treated by the neighbouring
`FinitePolynomialCategoryClassification` and
`FiniteHOLFormulaArithmetization` modules are therefore separate.
-/
import Dregg2.Tactics
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

namespace Dregg2.Metatheory.SmallCCCYonedaPresheaf

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

variable {C : Type u} [Category.{u} C]

/-! ## The limit-preserving fully faithful embedding -/

/-- Yoneda is fully faithful.  The one-universe assumption expresses
smallness; it is not a finiteness assumption. -/
def yonedaFullyFaithful : (yoneda (C := C)).FullyFaithful :=
  CategoryTheory.Yoneda.fullyFaithful

/-- Yoneda preserves the terminal object (indeed, it preserves all small
limits). -/
theorem yonedaPreservesTerminal :
    PreservesLimit (Functor.empty.{0} C) (yoneda (C := C)) := by
  infer_instance

/-- Yoneda preserves binary products (indeed, it preserves all small
limits). -/
theorem yonedaPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (yoneda (C := C)) := by
  infer_instance

/-! ## The pointwise representable-exponential equivalence -/

variable [CartesianMonoidalCategory C]
variable {A B X : C} [Closed A]

/-- Pointwise form of preservation of a representable exponential.

An element on the right is a family which sends `g : Y ⟶ A` and
`f : Y ⟶ X` naturally to a map `Y ⟶ B`.  The forward map uncurries
`h : X ⟶ B^A` and composes it with the product pairing `⟨g,f⟩`.  The
inverse evaluates such a family at the two projections from `A ⊗ X` and
then curries. -/
def representableExponentialEquiv (A B X : C) [Closed A] :
    (X ⟶ (ihom A).obj B) ≃
      ((yoneda.obj A).functorHom (yoneda.obj B)).obj (Opposite.op X) where
  toFun h :=
    { app := fun _ f ↦ ↾fun g ↦ lift g f.unop ≫ uncurry h
      naturality := by
        intro Y Z k f
        ext g
        change lift (k.unop ≫ g) (k.unop ≫ f.unop) ≫ uncurry h =
          k.unop ≫ lift g f.unop ≫ uncurry h
        rw [← Category.assoc, comp_lift] }
  invFun q :=
    curry (q.app (Opposite.op (A ⊗ X)) (snd A X).op (fst A X))
  left_inv h := by
    apply uncurry_injective
    simp
  right_inv q := by
    apply CategoryTheory.Functor.HomObj.ext
    funext Y f
    ext g
    dsimp
    rw [uncurry_curry]
    let k : Opposite.op (A ⊗ X) ⟶ Y :=
      (lift g f.unop).op
    have hf : (snd A X).op ≫ k = f := by
      apply Quiver.Hom.unop_inj
      simp [k]
    have hnat := q.naturality k (snd A X).op
    change (yoneda.obj A).map k ≫ q.app Y ((snd A X).op ≫ k) =
      q.app (Opposite.op (A ⊗ X)) (snd A X).op ≫ (yoneda.obj B).map k at hnat
    rw [hf] at hnat
    have happ := CategoryTheory.ConcreteCategory.congr_hom hnat (fst A X)
    simpa [k] using happ.symm

/-- The pointwise equivalences are natural in the probing object, hence form
an isomorphism of presheaves. -/
def representableExponentialIso (A B : C) [Closed A] :
    yoneda.obj ((ihom A).obj B) ≅
      (yoneda.obj A).functorHom (yoneda.obj B) :=
  NatIso.ofComponents
    (fun X ↦ (representableExponentialEquiv A B X.unop).toIso)
    (by
      intro X Y k
      ext h Z f g
      dsimp [representableExponentialEquiv, CategoryTheory.Functor.functorHom,
        CategoryTheory.Functor.homObjFunctor]
      change lift g f.unop ≫ uncurry (k.unop ≫ h) =
        lift g (f.unop ≫ k.unop) ≫ uncurry h
      rw [uncurry_natural_left]
      change lift g f.unop ≫ (A ◁ k.unop) ≫ uncurry h =
        lift g (f.unop ≫ k.unop) ≫ uncurry h
      rw [← Category.assoc, lift_whiskerLeft])

/-- In the cartesian closed structure chosen by mathlib on the presheaf
category, the preceding explicit internal hom is definitionally the
exponential `(y B)^(y A)`. -/
def yonedaExponentialIso (A B : C) [Closed A] :
    yoneda.obj ((ihom A).obj B) ≅
      (ihom (yoneda.obj A)).obj (yoneda.obj B) :=
  representableExponentialIso A B

/-- Headline specialization: when every object of `C` is closed, Yoneda sends
every chosen source exponential to the corresponding presheaf exponential. -/
def smallCCCYonedaExponentialIso [MonoidalClosed C] (A B : C) :
    yoneda.obj ((ihom A).obj B) ≅
      (ihom (yoneda.obj A)).obj (yoneda.obj B) :=
  yonedaExponentialIso A B

end

#assert_all_clean [yonedaFullyFaithful, yonedaPreservesTerminal,
  yonedaPreservesBinaryProducts, representableExponentialEquiv,
  representableExponentialIso, yonedaExponentialIso,
  smallCCCYonedaExponentialIso]

end Dregg2.Metatheory.SmallCCCYonedaPresheaf
