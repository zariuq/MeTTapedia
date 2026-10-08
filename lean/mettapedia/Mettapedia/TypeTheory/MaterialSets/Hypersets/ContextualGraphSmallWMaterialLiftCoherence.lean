import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWCarrierLift

/-!
# W compatibility with the common material family universe lift

The upper domain and dependent body coincide with the independently
constructed material family raising used for sums, products and identity.
Actual native maps compare the raised lower W family with the freshly
formed upper W family; their material carrier and whole-section squares
use the constructed W observation comparison.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWMaterialLiftCoherence

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphSmallWBranchSpan ContextualGraphSmallWSiteLift
open ContextualSmallFamilyWTypes ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphSmallWReadoutLift ContextualGraphSmallWCarrierLift
universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable (domainReading : NaturalHom (total domain) (values D))
variable (positionReading : NaturalHom (total (displayedBody domain body)) (values D))

def domainFamily : ContextualGraphMaterialFamilies.Family base := ⟨domain, domainReading⟩
def positionFamily : ContextualGraphMaterialFamilies.Family (total domain) := ⟨displayedBody domain body, positionReading⟩

theorem domain_native : upperDomain domain =
    (ContextualGraphMaterialLift.raise (domainFamily domain domainReading)).native := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem position_native : HEq (displayedBody (upperDomain domain) (upperBody domain body))
    (ContextualGraphMaterialLift.raisedBody (domainFamily domain domainReading)
      (positionFamily domain body positionReading)).native := by
  apply heq_of_eq
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem domain_reading : raisedDomainReading domain domainReading =
    (ContextualGraphMaterialLift.raise (domainFamily domain domainReading)).reading := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem position_reading : raisedPositionReading domain body positionReading =
    (ContextualGraphMaterialLift.raisedBody (domainFamily domain domainReading)
      (positionFamily domain body positionReading)).reading := by
  apply NaturalHom.ext
  intro _ _
  rfl

def forward : NaturalHom
    (ContextualGraphMaterialLift.raise (lowerFamily domain body domainReading positionReading)).native
    (upperFamily domain body domainReading positionReading).native where
  app point tree := (equiv domain body point).symm tree.down
  naturality step tree := inverse_natural domain body step tree.down

def backward : NaturalHom (upperFamily domain body domainReading positionReading).native
    (ContextualGraphMaterialLift.raise (lowerFamily domain body domainReading positionReading)).native where
  app point tree := ULift.up (equiv domain body point tree)
  naturality step tree := congrArg ULift.up (equiv_natural domain body step tree)

theorem forward_backward : (forward domain body domainReading positionReading).comp
    (backward domain body domainReading positionReading) =
      ContextualSmallMapConstructions.identity
        (ContextualGraphMaterialLift.raise (lowerFamily domain body domainReading positionReading)).native := by
  apply NaturalHom.ext
  intro point tree
  exact congrArg ULift.up ((equiv domain body point).apply_symm_apply tree.down)

theorem backward_forward : (backward domain body domainReading positionReading).comp
    (forward domain body domainReading positionReading) =
      ContextualSmallMapConstructions.identity (upperFamily domain body domainReading positionReading).native := by
  apply NaturalHom.ext
  intro point tree
  exact (equiv domain body point).symm_apply_apply tree

def material_square (point : (ContextualGraphMaterialLift.base base).Elements)
    (tree : (ContextualGraphMaterialLift.raise (lowerFamily domain body domainReading positionReading)).native.obj point) :
    Equal (ContextualGraphMaterialFamilies.termValue
      (ContextualGraphMaterialLift.raise (lowerFamily domain body domainReading positionReading)) point tree)
      (ContextualGraphMaterialFamilies.termValue (upperFamily domain body domainReading positionReading) point
        ((forward domain body domainReading positionReading).app point tree)) :=
  forwardComparison domain body domainReading positionReading point tree.down

def carrier_square (point : (ContextualGraphMaterialLift.base base).Elements) :
    Equal ((ContextualGraphMaterialProducts.carrier
      (ContextualGraphMaterialLift.raise (lowerFamily domain body domainReading positionReading))).app point.1 point.2)
      ((ContextualGraphMaterialProducts.carrier (upperFamily domain body domainReading positionReading)).app point.1 point.2) :=
  (ContextualGraphMaterialLift.carrierComparison (lowerFamily domain body domainReading positionReading)
    point.1 point.2.down).symm.trans (carrierComparison domain body domainReading positionReading point)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWMaterialLiftCoherence
