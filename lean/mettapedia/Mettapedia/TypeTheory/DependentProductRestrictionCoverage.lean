import Mettapedia.TypeTheory.DependentProductRestriction
import Mettapedia.TypeTheory.CategoryOfElementsBaseChange
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Final.Type

/-!
# Coverage of dependent arguments under theory restriction

A dependent function at a world is a natural section over its category of
future arrows and arguments. Initiality of the induced functor between those
categories makes the canonical restriction comparison a bijection.
An equivalence on the future undercategories is a sufficient condition;
an equivalence of whole theories is a special case. These conditions concern
substitution and evidence, not operational successor matching.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentProductRestrictionCoverage

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open DependentProductRestriction CategoryOfElementsBaseChange

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

abbrev futureArguments (A : C ⥤ Type u) (X : C) :=
  (Under.forget X ⋙ A).Elements

abbrev argumentProjection (A : C ⥤ Type u) (X : C) : futureArguments A X ⥤ A.Elements :=
  Functor.Elements.precomp (Under.forget X) A

private theorem section_natural (A : C ⥤ Type u) (B : A.Elements ⥤ Type u)
    {X Y Z : C} (value : DependentSection A B X) (step : Y ⟶ Z) (route : X ⟶ Y)
    (argument : A.obj Y) (next : A.obj Z) (same : A.map step argument = next) :
    B.map (CategoryOfElements.homMk ⟨Y, argument⟩ ⟨Z, next⟩ step same)
      (value.app Y route argument) = value.app Z (route ≫ step) next := by
  subst next
  exact value.naturality step route argument

def toFutureSection (A : C ⥤ Type u) (B : A.Elements ⥤ Type u) (X : C)
    (value : DependentSection A B X) : (argumentProjection A X ⋙ B).sections where
  val receipt := value.app receipt.1.right receipt.1.hom receipt.2
  property {first second} arrow := by
    have natural := section_natural A B value arrow.val.right first.1.hom
      first.2 second.2 arrow.property
    rw [Under.w arrow.val] at natural
    exact natural

def fromFutureSection (A : C ⥤ Type u) (B : A.Elements ⥤ Type u) (X : C)
    (value : (argumentProjection A X ⋙ B).sections) : DependentSection A B X where
  app _ arrow argument := value.val ⟨Under.mk arrow, argument⟩
  naturality {_ _} step arrow argument :=
    value.property (CategoryOfElements.homMk
      (⟨Under.mk arrow, argument⟩ : futureArguments A X)
      ⟨Under.mk (arrow ≫ step), A.map step argument⟩
      (Under.homMk step rfl) rfl)

def futureSectionEquiv (A : C ⥤ Type u) (B : A.Elements ⥤ Type u) (X : C) :
    DependentSection A B X ≃ (argumentProjection A X ⋙ B).sections where
  toFun := toFutureSection A B X
  invFun := fromFutureSection A B X
  left_inv value := by
    apply DependentSection.ext
    intro Y arrow argument
    rfl
  right_inv value := by
    apply Subtype.ext
    funext receipt
    congr 1

abbrev futureLift (F : C ⥤ D) (A : D ⥤ Type u) (X : C) :
    futureArguments (F ⋙ A) X ⥤ futureArguments A (F.obj X) :=
  Functor.Elements.precomp (Under.post (X := X) F) (Under.forget (F.obj X) ⋙ A)

theorem futureSection_restriction (F : C ⥤ D) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) (X : C) (value : DependentSection A B (F.obj X)) :
    toFutureSection (F ⋙ A) (restrictedFamily F A B) X (restrictSection F A B value) =
      (futureLift F A X).sectionsPrecomp (toFutureSection A B (F.obj X) value) := rfl

/-- The initial-functor theorem supplies both uniqueness and existence
of the evidence-bearing dependent-function extension. -/
theorem comparison_bijective (F : C ⥤ D) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) (X : C) [(futureLift F A X).Initial] :
    Function.Bijective (restrictSection F A B (X := X)) := by
  let target := futureSectionEquiv A B (F.obj X)
  let source := futureSectionEquiv (F ⋙ A) (restrictedFamily F A B) X
  have bijective := (futureLift F A X).bijective_sectionsPrecomp
    (argumentProjection A (F.obj X) ⋙ B)
  have factor : restrictSection F A B (X := X) =
      source.symm ∘ (futureLift F A X).sectionsPrecomp ∘ target := by
    funext value
    apply source.injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    exact futureSection_restriction F A B X value
  rw [factor]
  exact source.symm.bijective.comp (bijective.comp target.bijective)

noncomputable def futureLiftEquivalence (F : C ⥤ D) (A : D ⥤ Type u) (X : C)
    [(Under.post (X := X) F).IsEquivalence] :
    futureArguments (F ⋙ A) X ≌ futureArguments A (F.obj X) :=
  precompElementsEquivalence (Under.post (X := X) F).asEquivalence
    (Under.forget (F.obj X) ⋙ A)

noncomputable instance futureLift_isEquivalence (F : C ⥤ D) (A : D ⥤ Type u) (X : C)
    [(Under.post (X := X) F).IsEquivalence] : (futureLift F A X).IsEquivalence := by
  change (futureLiftEquivalence F A X).functor.IsEquivalence
  infer_instance

noncomputable def comparisonIso (F : C ⥤ D) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) [∀ X, (futureLift F A X).Initial] :
    F ⋙ dependentFunctions A B ≅ dependentFunctions (F ⋙ A) (restrictedFamily F A B) :=
  NatIso.ofComponents (fun X => (Equiv.ofBijective (restrictSection F A B)
      (comparison_bijective F A B X)).toIso)
    (by intro X Y step; exact (comparison F A B).naturality step)

theorem comparisonIso_hom (F : C ⥤ D) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) [∀ X, (futureLift F A X).Initial] :
    (comparisonIso F A B).hom = comparison F A B := rfl

end Mettapedia.TypeTheory.DependentProductRestrictionCoverage
