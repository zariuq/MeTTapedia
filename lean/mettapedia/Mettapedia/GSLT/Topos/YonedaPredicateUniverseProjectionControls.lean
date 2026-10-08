import Mettapedia.GSLT.Topos.YonedaPredicateUniverseProjection
import Mettapedia.GSLT.Topos.YonedaPredicateUniverseControls

/-!
# Original mixed-universe Cartesian and closed projection controls

The original diagram category has independently sized objects and arrows.
Its proper positive-output predicate admits a genuine shifted generalized
element. The actual Cartesian factor preserves that complete base map;
pulling the predicate back along the identity still rejects the identity.
The exponential comparison is invertible at these original endpoints,
and its evaluation equation retains the actual chosen evaluation map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Topos.YonedaPredicateUniverseProjectionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.GSLT.Core.LambdaTheoryClosedControls
open YonedaPredicateUniverseBridge YonedaPredicateUniverseControls
open YonedaPredicateUniverseProjection

local instance diagramsClosedChoice : MonoidalClosed Diagrams := inferInstance

local instance originalClosedChoice : MonoidalClosed (Original Diagrams) := inferInstance

local instance diagramsObjectClosed (A : Diagrams) : Closed A :=
  @MonoidalClosed.closed Diagrams _ _ diagramsClosedChoice A

local instance originalObjectClosed (A : Original Diagrams) : Closed A :=
  @MonoidalClosed.closed (Original Diagrams) _ _ originalClosedChoice A

theorem original_projection_fibered : (Original.projection Diagrams).IsFibered :=
  inferInstance

theorem original_projection_closed : MonoidalClosedFunctor (Original.projection Diagrams) :=
  inferInstance

def mixedProjectionMap := originalProjectionMap diagramsTheory

theorem mixed_projection_really_original :
    mixedProjectionMap.functor = Original.projection Diagrams := rfl

theorem shifted_lift_contains_identity :
    (𝟙 numbers) ∈ (liftDomain positive shift).predicate.obj (op numbers) := by
  change shift ∈ positiveOutput.obj (op numbers)
  exact positive_contains_shift

theorem identity_lift_still_excludes_identity :
    (𝟙 numbers) ∉ (liftDomain positive (𝟙 numbers)).predicate.obj (op numbers) := by
  intro held
  change (𝟙 numbers ≫ 𝟙 numbers) ∈ positiveOutput.obj (op numbers) at held
  have : (𝟙 numbers) ∈ positiveOutput.obj (op numbers) := by
    simpa only [Category.id_comp] using held
  exact identity_not_positive this

instance admittedShift_isHomLift :
    (Original.projection Diagrams).IsHomLift shift admittedShift := by
  change (Original.projection Diagrams).IsHomLift
    ((Original.projection Diagrams).map admittedShift) admittedShift
  infer_instance

def factoredShift : unrestricted ⟶ liftDomain positive shift :=
  Functor.IsStronglyCartesian.map (Original.projection Diagrams) shift (lift positive shift)
    (g := 𝟙 numbers) (Category.id_comp shift).symm admittedShift

instance factoredShift_isHomLift :
    (Original.projection Diagrams).IsHomLift (𝟙 numbers) factoredShift := by
  dsimp only [factoredShift]
  infer_instance

theorem factored_shift_complete : factoredShift ≫ lift positive shift = admittedShift :=
  Functor.IsStronglyCartesian.fac _ _ _ _ _

theorem factored_shift_base : factoredShift.base = 𝟙 numbers :=
  (IsHomLift.eq_of_isHomLift (Original.projection Diagrams)
    (a := unrestricted) (b := liftDomain positive shift) (𝟙 numbers) factoredShift).symm

theorem factor_then_projection_retains_eleven :
    ((Original.projection Diagrams).map (factoredShift ≫ lift positive shift)).app
      ⟨false⟩ (10 : Nat) = (11 : Nat) := by
  rw [factored_shift_complete]
  rfl

theorem omission_changes_complete_readout :
    ((Original.projection Diagrams).map (factoredShift ≫ lift positive shift)).app
        ⟨false⟩ (10 : Nat) ≠
      ((Original.projection Diagrams).map factoredShift).app ⟨false⟩ (10 : Nat) := by
  rw [factor_then_projection_retains_eleven]
  change (11 : Nat) ≠ factoredShift.base.app ⟨false⟩ (10 : Nat)
  rw [factored_shift_base]
  change (11 : Nat) ≠ 10
  omega

theorem original_exponential_comparison_invertible :
    IsIso ((expComparison (Original.projection Diagrams) positive).natTrans.app unrestricted) :=
  inferInstance

private def comparison (A B : Original Diagrams) :
    (Original.projection Diagrams).obj ((ihom A).obj B) ⟶
      (ihom ((Original.projection Diagrams).obj A)).obj
        ((Original.projection Diagrams).obj B) := by
  exact (expComparison (Original.projection Diagrams) A).natTrans.app B

private def targetEvaluation (A B : Original Diagrams) :
    (Original.projection Diagrams).obj A ⊗
        (ihom ((Original.projection Diagrams).obj A)).obj
          ((Original.projection Diagrams).obj B) ⟶
      (Original.projection Diagrams).obj B := by
  exact (ihom.ev ((Original.projection Diagrams).obj A)).app
    ((Original.projection Diagrams).obj B)

private def sourceEvaluation (A B : Original Diagrams) : A ⊗ (ihom A).obj B ⟶ B := by
  exact (ihom.ev A).app B

theorem original_exponential_evaluation (A B : Original Diagrams) :
    (Original.projection Diagrams).obj A ◁ comparison A B ≫ targetEvaluation A B =
      inv (CartesianMonoidalCategory.prodComparison (Original.projection Diagrams) A
        ((ihom A).obj B)) ≫ (Original.projection Diagrams).map (sourceEvaluation A B) := by
  exact expComparison_ev (Original.projection Diagrams) A B

end Mettapedia.GSLT.Topos.YonedaPredicateUniverseProjectionControls
