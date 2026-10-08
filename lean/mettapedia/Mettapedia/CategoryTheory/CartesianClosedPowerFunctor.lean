import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# A finite-limit-preserving functor that does not preserve exponentials

The power functor `X ↦ (I ⟶ X)` is the actual right adjoint to product with
`I`, so it preserves limits. Its canonical exponential comparison evaluates
each component using the same index. For two indices a coordinate-exchanging
function is outside this comparison's image. Thus finite-limit preservation
alone does not supply a closed functor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory.CartesianClosedPowerFunctor

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.CartesianMonoidalCategory

universe u

noncomputable section

def power (I : Type u) : Type u ⥤ Type u := ihom I


instance preservesLimits (I : Type u) : PreservesLimitsOfSize.{u, u} (power I) :=
  (ihom.adjunction I).rightAdjoint_preservesLimits

instance preservesFiniteLimits (I : Type u) : PreservesFiniteLimits (power I) :=
  inferInstance

/-- The canonical comparison, with its actual function carrier made explicit. -/
def comparison (I A B : Type u) :
    (I ⟶ (A ⟶ B)) ⟶ ((I ⟶ A) ⟶ (I ⟶ B)) :=
  (expComparison (power I) A).natTrans.app B


/-- The inverse of the actual product comparison, with the function carrier explicit. -/
def inverseProduct (I A B : Type u) :
    ((I ⟶ A) × (I ⟶ B)) ⟶ (I ⟶ A × B) := by
  let : PreservesLimit (pair A B) (power I) := inferInstance
  exact inv (CartesianMonoidalCategory.prodComparison (power I) A B)

theorem product_comparison_readout (I A B : Type u) (value : I ⟶ A × B) :
    CartesianMonoidalCategory.prodComparison (power I) A B value =
      (↾fun position => (value position).1, ↾fun position => (value position).2) := rfl

theorem product_inverse_readout (I A B : Type u) (first : I ⟶ A) (second : I ⟶ B)
    (position : I) :
    inverseProduct I A B (first, second) position =
      (first position, second position) := by
  let combined : I ⟶ A × B := ↾fun index => (first index, second index)
  have read : CartesianMonoidalCategory.prodComparison (power I) A B combined = (first, second) := rfl
  have inverse := congrArg (fun arrow => arrow combined)
    (IsIso.hom_inv_id (CartesianMonoidalCategory.prodComparison (power I) A B))
  change inverseProduct I A B
      (CartesianMonoidalCategory.prodComparison (power I) A B combined) = combined at inverse
  rw [read] at inverse
  exact congrArg (fun function : I ⟶ A × B => function position) inverse

/-- Read the actual comparison determined by the evaluation square. -/
theorem exponential_readout (I A B : Type u) (family : I ⟶ (A ⟶ B))
    (input : I ⟶ A) (position : I) :
    comparison I A B family input position =
      family position (input position) := by
  have observed := congrArg (fun arrow : ((I ⟶ A) × (I ⟶ (A ⟶ B))) ⟶ (I ⟶ B) =>
      arrow (input, family) position)
    (expComparison_ev (power I) A B)
  change comparison I A B family input position =
    (inverseProduct I A (A ⟶ B) (input, family) position).2
      ((inverseProduct I A (A ⟶ B) (input, family) position).1) at observed
  exact observed.trans (by rw [product_inverse_readout])

/-- This function reads the other coordinate of its supplied argument. -/
def exchange : (Bool ⟶ Bool) ⟶ (Bool ⟶ Bool) :=
  ↾fun input => ↾fun position => input (!position)

/-- The excluded function is an independently supplied complete function value. -/
theorem exponential_not_surjective :
    ¬ Function.Surjective (comparison Bool Bool Bool) := by
  intro surjective
  obtain ⟨family, target⟩ := surjective exchange
  let zero : Bool ⟶ Bool := ↾fun _ => false
  let inputIdentity : Bool ⟶ Bool := ↾fun position => position
  have zeroRead := exponential_readout Bool Bool Bool family zero false
  have identityRead := exponential_readout Bool Bool Bool family inputIdentity false
  have zeroTarget := congrArg (fun arrow : (Bool ⟶ Bool) ⟶ (Bool ⟶ Bool) => arrow zero false) target
  have identityTarget := congrArg (fun arrow : (Bool ⟶ Bool) ⟶ (Bool ⟶ Bool) => arrow inputIdentity false) target
  have first : family false false = false := zeroRead.symm.trans zeroTarget
  have second : family false false = true := identityRead.symm.trans identityTarget
  cases first.symm.trans second

theorem exponential_not_isIso :
    ¬ IsIso ((expComparison (power Bool) Bool).natTrans.app Bool) := by
  intro invertible
  let : IsIso (comparison Bool Bool Bool) := invertible
  apply exponential_not_surjective
  intro target
  refine ⟨inv (comparison Bool Bool Bool) target, ?_⟩
  exact congrArg (fun arrow => arrow target)
    (IsIso.inv_hom_id (comparison Bool Bool Bool))

theorem power_bool_not_closed : ¬ MonoidalClosedFunctor (power Bool) := by
  intro closed
  let := closed
  exact exponential_not_isIso inferInstance

end

end Mettapedia.CategoryTheory.CartesianClosedPowerFunctor
