import Mettapedia.GSLT.Topos.SubobjectClassifier
import Mettapedia.CategoryTheory.ElementaryToposGeometric
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Presheaf elementary topoi at a common universe bound

Objects and arrows of the indexing category may have different universe
sizes. The value carrier contains both sizes and an optional additional
bound. The actual category equivalence with the corresponding small
category transports the constructed sieve classifier. Cartesian closure
is the complete functor-to-types construction on the original category.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Topos.PresheafElementaryTopos

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

abbrev Carrier (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type (max u v w)

variable (C : Type u) [Category.{v} C]

/-- Only the indexing category is resized; presheaf values keep the common
carrier and every original restriction map. -/
def smallEquivalence : Carrier.{u,v,w} C ≌
    ((AsSmall.{w} C)ᵒᵖ ⥤ Type (max u v w)) :=
  (AsSmall.equiv : C ≌ AsSmall.{w} C).op.congrLeft

theorem smallEquivalence_value (P : Carrier.{u,v,w} C) (X : C) :
    ((smallEquivalence C).functor.obj P).obj
      (Opposite.op ((AsSmall.up : C ⥤ AsSmall.{w} C).obj X)) =
        P.obj (Opposite.op X) := rfl

theorem smallEquivalence_map (P : Carrier.{u,v,w} C) {X Y : C}
    (arrow : X ⟶ Y) :
    ((smallEquivalence C).functor.obj P).map
      ((AsSmall.up : C ⥤ AsSmall.{w} C).map arrow).op = P.map arrow.op := rfl

/-- The small presentation has the actual sieve classifier, constructed
from its characteristic-map/subobject representation. -/
def smallClassifier : Subobject.Classifier ((AsSmall.{w} C)ᵒᵖ ⥤ Type (max u v w)) :=
  SubobjectRepresentableBy.classifier
    (presheafSubobjectRepresentableByOmega (AsSmall.{w} C))

/-- Both classification and uniqueness are transported through the full
category equivalence, without assuming classifier existence. -/
def classifier : Subobject.Classifier (Carrier.{u,v,w} C) :=
  (smallClassifier C).ofEquivalence (smallEquivalence C).symm

def object : Mettapedia.CategoryTheory.ElementaryTopos.{(max u v w)+1,max u v w} := by
  let : MonoidalClosed (Carrier.{u,v,w} C) := FunctorToTypes.monoidalClosed.{w,v,u}
  exact Mettapedia.CategoryTheory.ElementaryTopos.ofCategory
    (Carrier.{u,v,w} C) (classifier C)

/-- The supplied classifier square is an actual pullback for every mono. -/
theorem classifies {U X : Carrier.{u,v,w} C} (inclusion : U ⟶ X) [Mono inclusion] :
    IsPullback inclusion ((classifier C).χ₀ U)
      ((classifier C).χ inclusion) (classifier C).truth :=
  (classifier C).isPullback inclusion

/-- A competing pullback square has the same complete characteristic map. -/
theorem classification_unique {U X : Carrier.{u,v,w} C} (inclusion : U ⟶ X)
    [Mono inclusion] (name : X ⟶ (classifier C).Ω)
    (witness : U ⟶ (classifier C).Ω₀)
    (square : IsPullback inclusion witness name (classifier C).truth) :
    name = (classifier C).χ inclusion :=
  (classifier C).uniq inclusion square

end Mettapedia.GSLT.Topos.PresheafElementaryTopos
