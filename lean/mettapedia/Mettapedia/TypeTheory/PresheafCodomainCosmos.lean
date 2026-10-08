import Mettapedia.CategoryTheory.ArrowDiagrams
import Mettapedia.TypeTheory.PresheafDependentAdjunction
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Cosmic structure of the presheaf codomain category

Dependent types and their commuting program--certificate squares form the
actual arrow category of presheaves. Its equivalence with length-one diagrams
transfers small limits and colimits, and transfers the cartesian closed
structure of the complete functor category. The dependent adjunctions remain
the existing family-derived slice adjunctions; closure of the total category
does not identify a dependent function with a predicate of inhabitation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafCodomainCosmos

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.Computability.ComputationalTrinity

universe u
variable (C : Type u) [Category.{u} C]

abbrev Total := Arrow (Face.{u, u, u} C)

noncomputable instance complete : HasLimitsOfSize.{u, u} (Total C) :=
  Adjunction.has_limits_of_equivalence
    (Mettapedia.CategoryTheory.ArrowDiagrams.equivalence (Face.{u, u, u} C)).inverse

noncomputable instance cocomplete : HasColimitsOfSize.{u, u} (Total C) :=
  Adjunction.has_colimits_of_equivalence
    (Mettapedia.CategoryTheory.ArrowDiagrams.equivalence (Face.{u, u, u} C)).inverse

noncomputable instance cartesian : CartesianMonoidalCategory (Total C) :=
  CartesianMonoidalCategory.ofHasFiniteProducts

noncomputable instance closed : MonoidalClosed (Total C) := by
  letI : MonoidalClosed (ComposableArrows (Face.{u, u, u} C) 1) :=
    Functor.functorCategoryMonoidalClosed (Fin 2) (Face.{u, u, u} C)
  exact cartesianClosedOfEquiv
    (Mettapedia.CategoryTheory.ArrowDiagrams.equivalence (Face.{u, u, u} C))

/-- Codomain keeps the program index of each dependent specification. -/
def codomain : Total C ⥤ Face.{u, u, u} C := Arrow.rightFunc

/-- The actual codomain projection is endpoint evaluation under the arrow
comparison, including both components of commuting squares. -/
def codomainAsEvaluation :
    Mettapedia.CategoryTheory.ArrowDiagrams.toDiagrams (Face.{u, u, u} C) ⋙
        (evaluation (Fin 2) (Face.{u, u, u} C)).obj 1 ≅ codomain C :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro first second square
    change square.right ≫ 𝟙 _ = 𝟙 _ ≫ square.right
    simp)

instance codomain_preservesLimits : PreservesLimitsOfSize.{u, u} (codomain C) := by
  have : (Mettapedia.CategoryTheory.ArrowDiagrams.toDiagrams
      (Face.{u, u, u} C)).IsEquivalence :=
    (Mettapedia.CategoryTheory.ArrowDiagrams.equivalence (Face.{u, u, u} C)).isEquivalence_inverse
  exact preservesLimits_of_natIso (codomainAsEvaluation C)

instance codomain_preservesColimits : PreservesColimitsOfSize.{u, u} (codomain C) := by
  have : (Mettapedia.CategoryTheory.ArrowDiagrams.toDiagrams
      (Face.{u, u, u} C)).IsEquivalence :=
    (Mettapedia.CategoryTheory.ArrowDiagrams.equivalence (Face.{u, u, u} C)).isEquivalence_inverse
  exact preservesColimits_of_natIso (codomainAsEvaluation C)

noncomputable def exponential (domain : Total C) : Total C ⥤ Total C := ihom domain

noncomputable def homEquiv (domain codomain argument : Total C) :
    (domain ⊗ argument ⟶ codomain) ≃ (argument ⟶ (exponential C domain).obj codomain) :=
  (ihom.adjunction domain).homEquiv argument codomain

theorem beta {domain codomain argument : Total C}
    (body : domain ⊗ argument ⟶ codomain) :
    MonoidalClosed.uncurry (homEquiv C domain codomain argument body) = body :=
  (homEquiv C domain codomain argument).symm_apply_apply body

theorem eta {domain codomain argument : Total C}
    (function : argument ⟶ (exponential C domain).obj codomain) :
    homEquiv C domain codomain argument (MonoidalClosed.uncurry function) = function :=
  (homEquiv C domain codomain argument).apply_symm_apply function

theorem function_unique {domain codomain argument : Total C}
    (body : domain ⊗ argument ⟶ codomain)
    (function : argument ⟶ (exponential C domain).obj codomain)
    (computes : MonoidalClosed.uncurry function = body) :
    function = homEquiv C domain codomain argument body := by
  rw [← computes, eta]

end Mettapedia.TypeTheory.PresheafCodomainCosmos
