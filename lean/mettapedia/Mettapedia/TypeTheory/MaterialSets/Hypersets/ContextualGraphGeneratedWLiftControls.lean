import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWSubstitutionControls

/-!
# Growing generated W families across the actual material universe raise

The authored continuation W remains empty initially and later inhabited
in the independently formed upper family. Material carrier and whole
native tree comparisons are instantiated in that same model. A second
control retains two distinct parameter occurrences whose lower and upper
material readings match, so universe raising does not turn observational
agreement into native identity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWLiftControls

open CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyWTypes
open ContextualGraphDiagrams ContextualRealizedGraphs
open ConstructiveObservedMaterialControls
open ContextualGraphGeneratedWControls (domainCode bodyCode domainReading bodyReading leaf)

abbrev upperFamily := ContextualGraphGeneratedWLift.upperFamily domainCode bodyCode domainReading bodyReading
abbrev upperReceipts := ContextualGraphGeneratedWLift.upperLiteral domainCode bodyCode domainReading bodyReading

def upperTask (stage : Nat) := (ContextualGraphMaterialLift.elementsUp params).obj (task stage)

def upperLeaf : upperFamily.native.obj (upperTask 2) :=
  (ContextualGraphSmallWSiteLift.equiv domain.native (domain.bodyNative body) (upperTask 2)).symm
    (leaf 2 2 (by decide) (by decide))

def upperReceipt : upperReceipts.obj (upperTask 2) :=
  ContextualGraphFamilyBodies.encode upperFamily.native upperFamily.reading (upperTask 2) upperLeaf

theorem upper_generated_family_varies : ¬ Nonempty (upperReceipts.obj (upperTask 0)) ∧
    Nonempty (upperReceipts.obj (upperTask 2)) := by
  refine ⟨?_, ⟨upperReceipt⟩⟩
  rintro ⟨receipt⟩
  exact initial_W_empty ⟨ContextualGraphGeneratedWLift.decoder domainCode bodyCode domainReading bodyReading (upperTask 0) receipt⟩

def material_carrier_square (stage : Nat) :=
  ContextualGraphGeneratedWLift.carrier_square domainCode bodyCode domainReading bodyReading (upperTask stage)

def actual_upper_member : Member (upperFamily.reading.app (upperTask 2).1 ⟨(upperTask 2).2, upperLeaf⟩)
    ((ContextualGraphMaterialProducts.carrier upperFamily).app (upperTask 2).1 (upperTask 2).2) :=
  ContextualGraphFamilyBodyComparison.memberIntro upperFamily.native upperFamily.reading (upperTask 2) _ upperLeaf (Equal.refl _)

namespace DuplicateOccurrences
open ContextualGraphSmallWSubstitutionControls

abbrev repeatedDomain := ContextualGraphSmallWReadoutSubstitution.newDomain ContextualGraphSmallWSubstitutionControls.forget oldDomain
abbrev repeatedBody := ContextualGraphSmallWReadoutSubstitution.newBody ContextualGraphSmallWSubstitutionControls.forget oldDomain oldBody
abbrev repeatedDomainReading := ContextualGraphSmallWReadoutSubstitution.domainReadingUnder ContextualGraphSmallWSubstitutionControls.forget oldDomain
  ContextualGraphSmallWSubstitutionControls.domainReading
abbrev repeatedPositionReading := ContextualGraphSmallWReadoutSubstitution.positionReadingUnder ContextualGraphSmallWSubstitutionControls.forget oldDomain oldBody
  ContextualGraphSmallWSubstitutionControls.positionReading

abbrev raised := ContextualGraphSmallWCarrierLift.upperFamily repeatedDomain repeatedBody repeatedDomainReading repeatedPositionReading

def leftPoint := (ContextualGraphMaterialLift.elementsUp duplicated).obj (ContextualGraphSmallWSubstitutionControls.leftPoint 2)
def rightPoint := (ContextualGraphMaterialLift.elementsUp duplicated).obj (ContextualGraphSmallWSubstitutionControls.rightPoint 2)

def leftTree : raised.native.obj leftPoint :=
  (ContextualGraphSmallWSiteLift.equiv repeatedDomain repeatedBody leftPoint).symm
    ContextualGraphSmallWSubstitutionControls.leftTree

def rightTree : raised.native.obj rightPoint :=
  (ContextualGraphSmallWSiteLift.equiv repeatedDomain repeatedBody rightPoint).symm
    ContextualGraphSmallWSubstitutionControls.rightTree

def readings_match : Equal (raised.reading.app leftPoint.1 ⟨leftPoint.2, leftTree⟩)
    (raised.reading.app rightPoint.1 ⟨rightPoint.2, rightTree⟩) :=
  (ContextualGraphSmallWCarrierLift.forwardComparison repeatedDomain repeatedBody repeatedDomainReading repeatedPositionReading
    leftPoint ContextualGraphSmallWSubstitutionControls.leftTree).symm.trans
      ((ContextualGraphUniverseLift.preserve ContextualGraphSmallWSubstitutionControls.material_trees_match).trans
        (ContextualGraphSmallWCarrierLift.forwardComparison repeatedDomain repeatedBody repeatedDomainReading repeatedPositionReading
          rightPoint ContextualGraphSmallWSubstitutionControls.rightTree))

theorem receipts_distinct : (⟨leftPoint.2, leftTree⟩ : (total raised.native).obj leftPoint.1) ≠
    ⟨rightPoint.2, rightTree⟩ := by
  intro same
  exact parameter_occurrences_distinct (congrArg (fun receipt => receipt.1.down) same)

theorem material_matching_is_not_literal_identity :
    Nonempty (Equal (raised.reading.app leftPoint.1 ⟨leftPoint.2, leftTree⟩)
      (raised.reading.app rightPoint.1 ⟨rightPoint.2, rightTree⟩)) ∧
    (⟨leftPoint.2, leftTree⟩ : (total raised.native).obj leftPoint.1) ≠ ⟨rightPoint.2, rightTree⟩ :=
  ⟨⟨readings_match⟩, receipts_distinct⟩

end DuplicateOccurrences

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWLiftControls
