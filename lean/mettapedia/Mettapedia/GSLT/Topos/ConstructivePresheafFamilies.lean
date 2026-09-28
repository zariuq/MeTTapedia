import Mettapedia.GSLT.Topos.ConstructivePresheafFunctions
import Mathlib.CategoryTheory.Elements

/-!
# Predicate families over a category of elements

A predicate on parameter/value pairs is equivalently a predicate family
over the parameter presheaf's category of elements. Parameters may vary
with the world; they need not extend to global natural sections.

The equivalence retains the value and the actual restriction arrow. Taking
the subtype of a predicate retains its support, not distinct proof histories.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf

open CategoryTheory
open scoped ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]
variable (H F : C ⥤ Type u)

/-- Values indexed by worlds carrying a particular parameter. -/
def overElements : H.Elements ⥤ Type u :=
  restrict (CategoryOfElements.π H) F

variable {H F}

/-- Regard a predicate on pairs as a family at each parameter. -/
def familyPredicate (predicate : Subfunctor (FunctorToTypes.prod H F)) :
    Subfunctor (overElements H F) where
  obj X := {value | (X.2, value) ∈ predicate.obj X.1}
  map {X Y} restriction := by
    intro value member
    have held := predicate.map restriction.val member
    change (H.map restriction.val X.2, F.map restriction.val value) ∈ predicate.obj Y.1 at held
    rw [restriction.property] at held
    exact held

/-- Recover the joint predicate without choosing any parameter or value. -/
def totalPredicate (predicate : Subfunctor (overElements H F)) :
    Subfunctor (FunctorToTypes.prod H F) where
  obj X := {pair | pair.2 ∈ predicate.obj ⟨X, pair.1⟩}
  map {X Y} restriction := by
    intro pair member
    exact predicate.map
      (CategoryOfElements.homMk ⟨X, pair.1⟩ ⟨Y, H.map restriction pair.1⟩ restriction rfl) member

theorem family_totalPredicate (predicate : Subfunctor (overElements H F)) :
    familyPredicate (totalPredicate predicate) = predicate := by
  apply Subfunctor.ext
  funext X
  cases X
  rfl

theorem total_familyPredicate (predicate : Subfunctor (FunctorToTypes.prod H F)) :
    totalPredicate (familyPredicate predicate) = predicate := by
  apply Subfunctor.ext
  funext X
  funext pair
  cases pair
  rfl

theorem familyPredicate_le_iff
    (left right : Subfunctor (FunctorToTypes.prod H F)) :
    familyPredicate left ≤ familyPredicate right ↔ left ≤ right := by
  constructor
  · intro held X pair member
    exact held ⟨X, pair.1⟩ member
  · intro held X value member
    exact held X.1 member

/-- The parameterwise and joint descriptions carry precisely the same predicates. -/
def predicateFamilyEquiv (H F : C ⥤ Type u) :
    Subfunctor (FunctorToTypes.prod H F) ≃ Subfunctor (overElements H F) where
  toFun := familyPredicate
  invFun := totalPredicate
  left_inv := total_familyPredicate
  right_inv := family_totalPredicate

/-- The actual supported values form a presheaf over parameterized worlds. -/
def supportedFamily (predicate : Subfunctor (FunctorToTypes.prod H F)) :
    H.Elements ⥤ Type u :=
  (familyPredicate predicate).toFunctor

theorem supportedFamily_map_value (predicate : Subfunctor (FunctorToTypes.prod H F))
    {X Y : H.Elements} (restriction : X ⟶ Y)
    (value : (supportedFamily predicate).obj X) :
    ((supportedFamily predicate).map restriction value).val = F.map restriction.val value.val := rfl

end Mettapedia.GSLT.Topos.ConstructivePresheaf
