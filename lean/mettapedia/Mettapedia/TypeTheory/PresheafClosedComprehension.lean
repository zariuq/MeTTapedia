import Mettapedia.TypeTheory.PresheafCodomainCosmos
import Mettapedia.CategoryTheory.OverPullbackFrobenius

/-!
# Closed comprehension for presheaf dependent specifications

The actual presheaf slices are cartesian closed via the equivalence with
families on the category of elements. Actual pullback between these slices
preserves exponentials by the canonical Frobenius comparison. Together with
the existing dependent sum and dependent product adjunctions, this supplies
the closed codomain semantics along every natural program map inside a
fixed presheaf category.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafClosedComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafSlice

universe u
variable {C : Type u} [Category.{u} C]

noncomputable instance slice_cartesian (P : Face.{u, u, u} C) :
    CartesianMonoidalCategory (Over P) := Over.cartesianMonoidalCategory P

noncomputable instance family_closed (P : Face.{u, u, u} C) :
    MonoidalClosed (DisplayedFamily.{u, u, u, u} P) :=
  Functor.functorCategoryMonoidalClosed P.Elements (Type u)

noncomputable instance slice_closed (P : Face.{u, u, u} C) :
    MonoidalClosed (Over P) := cartesianClosedOfEquiv (equivalence P)

noncomputable abbrev substitution {P Q : Face.{u, u, u} C} (f : Q ⟶ P) :
    Over P ⥤ Over Q := Over.pullback f

instance substitution_preservesLimits {P Q : Face.{u, u, u} C} (f : Q ⟶ P) :
    PreservesLimitsOfSize.{u, u} (substitution f) :=
  (Over.mapPullbackAdj f).rightAdjoint_preservesLimits

noncomputable instance substitution_closed {P Q : Face.{u, u, u} C} (f : Q ⟶ P) :
    MonoidalClosedFunctor (substitution f) :=
  Mettapedia.CategoryTheory.OverPullbackFrobenius.pullback_closed f

noncomputable def exponentialComparison {P Q : Face.{u, u, u} C}
    (f : Q ⟶ P) (A B : Over P) :
    (substitution f).obj ((ihom A).obj B) ≅
      (ihom ((substitution f).obj A)).obj ((substitution f).obj B) :=
  asIso ((expComparison (substitution f) A).natTrans.app B)

/-- Evaluation after the comparison is evaluation before substitution,
with the canonical product comparison retained. -/
theorem exponential_evaluation {P Q : Face.{u, u, u} C}
    (f : Q ⟶ P) (A B : Over P) :
    MonoidalCategory.whiskerLeft ((substitution f).obj A) (exponentialComparison f A B).hom ≫
        (ihom.ev ((substitution f).obj A)).app ((substitution f).obj B) =
      inv (CartesianMonoidalCategory.prodComparison (substitution f) A ((ihom A).obj B)) ≫
        (substitution f).map ((ihom.ev A).app B) :=
  expComparison_ev (substitution f) A B

noncomputable def adjointTriple {P Q : Face.{u, u, u} C} (f : Q ⟶ P) :
    (Over.map f ⊣ substitution f) ×
      (substitution f ⊣ PresheafDependentAdjunction.dependentProduct f) :=
  PresheafDependentAdjunction.adjointTriple f

end Mettapedia.TypeTheory.PresheafClosedComprehension
