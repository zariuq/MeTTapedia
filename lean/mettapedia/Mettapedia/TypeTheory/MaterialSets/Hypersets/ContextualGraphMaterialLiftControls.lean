import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftFunctional
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalControls

/-!
# Growing observed sum and product controls across the universe shift

The actual observed domain grows at every stage. Its independent upper
sums and compatible products agree with the lifted lower material bodies.
Identity and occurrence-flipping functions remain materially equal but
have distinct native receipts. The result-sensitive incompatible function
is still excluded after raising.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftControls

open CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphMaterialFamilies ContextualGraphMaterialProducts ContextualGraphMaterialFunctionalProducts
open ContextualGraphMaterialLift ContextualGraphMaterialObservedControls
open PowerClassPresheafDescent.Controls ConstructiveObservedMaterialControls

def point (stage : Nat) : (base parameters).Elements := (elementsUp parameters).obj (parameter stage)

def pointStep {first second : Nat} (order : first ≤ second) : point first ⟶ point second :=
  (elementsUp parameters).map (parameterStep order)

theorem upper_domain_grows (stage : Nat) :
    ¬ ∃ previous : (raise domainFamily).native.obj (point stage),
      (raise domainFamily).native.map (pointStep (Nat.le_succ stage)) previous =
        ULift.up (stageValue (stage+1) (stage+1) (by omega) false) := by
  rintro ⟨previous, same⟩
  exact domain_grows stage ⟨previous.down, congrArg ULift.down same⟩

def sumComparison (stage : Nat) :
    Equal (ContextualGraphUniverseLift.value
      ((carrier (sigma domainFamily bodyFamily)).app (world stage) PUnit.unit))
      ((carrier (ContextualGraphMaterialLiftSums.upper domainFamily bodyFamily)).app
        (point stage).1 (point stage).2) :=
  ContextualGraphMaterialLiftSums.carrierComparison domainFamily bodyFamily (point stage)

def compatibleProductComparison (stage : Nat) :
    Equal (ContextualGraphUniverseLift.value
      ((carrier (functionalPi domainFamily bodyFamily)).app (world stage) PUnit.unit))
      ((carrier (ContextualGraphMaterialLiftFunctional.upper domainFamily bodyFamily)).app
        (point stage).1 (point stage).2) :=
  ContextualGraphMaterialLiftFunctional.carrierComparison domainFamily bodyFamily (point stage)

def upperIdentity (stage : Nat) :
    (ContextualGraphMaterialLiftFunctional.upper domainFamily bodyFamily).native.obj (point stage) :=
  (ContextualGraphMaterialLiftFunctional.backward domainFamily bodyFamily).app (point stage)
    (ULift.up (ContextualGraphMaterialFunctionalControls.compatibleIdentity.val (parameter stage)))

def upperFlip (stage : Nat) :
    (ContextualGraphMaterialLiftFunctional.upper domainFamily bodyFamily).native.obj (point stage) :=
  (ContextualGraphMaterialLiftFunctional.backward domainFamily bodyFamily).app (point stage)
    (ULift.up (ContextualGraphMaterialFunctionalControls.compatibleFlip.val (parameter stage)))

theorem compatible_identity_every_stage (stage : Nat) :
    Nonempty ((ContextualGraphMaterialLiftFunctional.upper domainFamily bodyFamily).native.obj (point stage)) :=
  ⟨upperIdentity stage⟩

def identityFlipMatching (stage : Nat) :
    Equal
      (termValue (ContextualGraphMaterialLiftFunctional.upper domainFamily bodyFamily) (point stage) (upperIdentity stage))
      (termValue (ContextualGraphMaterialLiftFunctional.upper domainFamily bodyFamily) (point stage) (upperFlip stage)) :=
  (ContextualGraphMaterialLiftFunctional.inverseReading domainFamily bodyFamily (point stage)
    (ULift.up (ContextualGraphMaterialFunctionalControls.compatibleIdentity.val (parameter stage)))).symm.trans
      ((ContextualGraphUniverseLift.preserve (ContextualGraphMaterialFunctionalControls.identityFlipMatching
        (parameter stage))).trans
        (ContextualGraphMaterialLiftFunctional.inverseReading domainFamily bodyFamily (point stage)
          (ULift.up (ContextualGraphMaterialFunctionalControls.compatibleFlip.val (parameter stage)))))

theorem compatible_receipts_still_distinct : upperIdentity 0 ≠ upperFlip 0 := by
  intro same
  exact ContextualGraphMaterialFunctionalControls.compatible_receipts_distinct
    (congrArg ULift.down ((ContextualGraphMaterialLiftFunctional.nativeEquiv domainFamily bodyFamily (point 0)).symm.injective same))

def upperSensitive :
    (ContextualGraphMaterialLiftProducts.upper domainFamily bodyFamily).native.obj (point 3) :=
  (ContextualGraphMaterialLiftProducts.backward domainFamily bodyFamily).app (point 3)
    (ULift.up (sensitiveFunction.val (parameter 3)))

theorem incompatible_still_excluded :
    ¬ ∃ function : (ContextualGraphMaterialLiftFunctional.upper domainFamily bodyFamily).native.obj (point 3),
      function.val = upperSensitive := by
  rintro ⟨function, same⟩
  apply ContextualGraphMaterialFunctionalControls.incompatible_section_excluded
  refine ⟨((ContextualGraphMaterialLiftFunctional.forward domainFamily bodyFamily).app (point 3) function).down, ?_⟩
  exact (congrArg (fun term => ((ContextualGraphMaterialLiftProducts.forward domainFamily bodyFamily).app
    (point 3) term).down) same).trans
      (congrArg ULift.down ((ContextualGraphMaterialLiftProducts.nativeEquiv domainFamily bodyFamily (point 3)).apply_symm_apply
        (ULift.up (sensitiveFunction.val (parameter 3)))))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftControls
