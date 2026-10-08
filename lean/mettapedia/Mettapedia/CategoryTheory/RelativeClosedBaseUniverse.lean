import Mettapedia.CategoryTheory.RelativeClosedBaseConservativity
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Universe transport for closed base conservativity

The common-universe reconstruction can be used for a category with
independent object and arrow universes by first taking its genuine
equivalent small presentation. Finite limits and closedness transport
through that equivalence. Composing with generated-base conservativity
retains every original arrow and all formal object comparisons.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.UniversePresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable (C : Type u) [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

instance finite : HasFiniteLimits (AsSmall.{0} C) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (AsSmall.equiv (C := C)).inverse

noncomputable instance cartesian : CartesianMonoidalCategory (AsSmall.{0} C) :=
  CartesianMonoidalCategory.ofHasFiniteProducts

noncomputable instance closed : MonoidalClosed (AsSmall.{0} C) :=
  cartesianClosedOfEquiv (AsSmall.equiv (C := C))

abbrev Guest := Conservativity.Guest (C := AsSmall.{0} C)

def equivalence : C ≌ Guest C :=
  (AsSmall.equiv (C := C)).trans (Conservativity.equivalence (C := AsSmall.{0} C))

abbrev inclusion : C ⥤ Guest C := (equivalence C).functor

instance faithful : (inclusion C).Faithful := (equivalence C).faithful_functor

instance full : (inclusion C).Full := (equivalence C).full_functor

def original_arrow_equivalence (source target : C) :
    (source ⟶ target) ≃ ((inclusion C).obj source ⟶ (inclusion C).obj target) :=
  (equivalence C).fullyFaithfulFunctor.homEquiv

theorem original_arrow_equality_iff {source target : C} (first second : source ⟶ target) :
    (inclusion C).map first = (inclusion C).map second ↔ first = second :=
  ⟨fun same => (inclusion C).map_injective same,
    fun same => congrArg (inclusion C).map same⟩

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.UniversePresentation
