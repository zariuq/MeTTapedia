import Mettapedia.CategoryTheory.ElementaryToposSliceExponentials
import Mettapedia.CategoryTheory.OverPullbackFrobenius
import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Dependent products in elementary topoi

The actual slice pullback functor is identified with the product-to-slice
functor followed by the iterated-slice equivalence. The section adjunction
in the earned cartesian closed slice supplies its right adjoint. Thus the
dependent product requires no pre-existing local closedness or pullback
right-adjoint capability.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposDependentProducts

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasPullbacks C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C)
variable {X B : C} (f : X ⟶ B)

attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Over.braidedCategory

/-- The comparison uses the actual composition/pullback adjunction and
the actual iterated-slice equivalence. -/
def productPullbackComparison :
    toOver (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ Over.pullback f :=
  conjugateIsoEquiv
    ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjToOver _))
    (Over.mapPullbackAdj f)
    (eqToIso (Over.iteratedSliceBackward_forget (Over.mk f)))

/-- A concrete dependent-product functor on the standard chosen slices. -/
def dependentProduct : Over X ⥤ Over B :=
  letI : MonoidalClosed (Over B) :=
    ElementaryToposSliceExponentials.monoidalClosed classifier B
  letI : ChosenPullbacksAlong (curryRightUnitorHom (Over.mk f)) :=
    ChosenPullbacksAlong.ofHasPullbacksAlong _
  (Over.mk f).iteratedSliceBackward ⋙ Over.sections (Over.mk f)

/-- Arbitrary actual slice pullback has the constructed dependent-product
right adjoint. Both adjunctions used here have earned universal properties. -/
def pullbackAdjunction : Over.pullback f ⊣ dependentProduct classifier f := by
  letI : MonoidalClosed (Over B) :=
    ElementaryToposSliceExponentials.monoidalClosed classifier B
  letI : ChosenPullbacksAlong (curryRightUnitorHom (Over.mk f)) :=
    ChosenPullbacksAlong.ofHasPullbacksAlong _
  exact ((Over.toOverSectionsAdj (Over.mk f)).comp
    (Over.mk f).iteratedSliceEquiv.toAdjunction).ofNatIsoLeft
    (productPullbackComparison f)

include classifier in
/-- The left-adjoint property is derived, not required of the pullback. -/
theorem pullback_isLeftAdjoint : (Over.pullback f).IsLeftAdjoint :=
  ⟨dependentProduct classifier f, ⟨pullbackAdjunction classifier f⟩⟩

/-- The complete dependent transpose retains the actual slice body. -/
def dependentCurry {context : Over B} {target : Over X}
    (body : (Over.pullback f).obj context ⟶ target) :
    context ⟶ (dependentProduct classifier f).obj target :=
  (pullbackAdjunction classifier f).homEquiv context target body

def dependentUncurry {context : Over B} {target : Over X}
    (function : context ⟶ (dependentProduct classifier f).obj target) :
    (Over.pullback f).obj context ⟶ target :=
  ((pullbackAdjunction classifier f).homEquiv context target).symm function

theorem dependent_beta {context : Over B} {target : Over X}
    (body : (Over.pullback f).obj context ⟶ target) :
    dependentUncurry classifier f (dependentCurry classifier f body) = body :=
  ((pullbackAdjunction classifier f).homEquiv context target).symm_apply_apply body

theorem dependent_eta {context : Over B} {target : Over X}
    (function : context ⟶ (dependentProduct classifier f).obj target) :
    dependentCurry classifier f (dependentUncurry classifier f function) = function :=
  ((pullbackAdjunction classifier f).homEquiv context target).apply_symm_apply function

/-- Complete dependent transposition commutes with every actual source
substitution, including the chosen pullback's component map. -/
theorem dependentCurry_substitution {earlier later : Over B} {target : Over X}
    (arrow : earlier ⟶ later) (body : (Over.pullback f).obj later ⟶ target) :
    dependentCurry classifier f ((Over.pullback f).map arrow ≫ body) =
      arrow ≫ dependentCurry classifier f body :=
  (pullbackAdjunction classifier f).homEquiv_naturality_left arrow body

/-- Any independently supplied choice of pullbacks has the earned
dependent product after its canonical comparison to the standard choice. -/
@[instance_reducible]
def exponentiable [ChosenPullbacksAlong f] : ExponentiableMorphism f where
  pushforward := dependentProduct classifier f
  pullbackPushforwardAdj := (pullbackAdjunction classifier f).ofNatIsoLeft
    (ChosenPullbacksAlong.pullbackIsoOverPullback f).symm

/-- The canonical exponential comparison of the actual pullback is
invertible for the constructed source and target closed structures. -/
theorem pullbackClosed :
    letI : MonoidalClosed (Over B) :=
      ElementaryToposSliceExponentials.monoidalClosed classifier B
    letI : MonoidalClosed (Over X) :=
      ElementaryToposSliceExponentials.monoidalClosed classifier X
    MonoidalClosedFunctor (Over.pullback f) := by
  let : MonoidalClosed (Over B) :=
    ElementaryToposSliceExponentials.monoidalClosed classifier B
  let : MonoidalClosed (Over X) :=
    ElementaryToposSliceExponentials.monoidalClosed classifier X
  exact OverPullbackFrobenius.pullback_closed f

end Mettapedia.CategoryTheory.ElementaryToposDependentProducts
