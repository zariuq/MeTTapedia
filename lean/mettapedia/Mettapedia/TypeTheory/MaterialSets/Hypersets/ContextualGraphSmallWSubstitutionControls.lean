import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadoutSubstitution
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWControls

/-!
# Noninjective W substitution on the growing observed model

Two distinct parameter occurrences are sent to the same authored task.
The independently constructed W bodies and carriers match, while the
literal parameters remain distinct. The same substituted family is empty
initially and later inhabited, so the comparison is not a constant-family
or empty-carrier instance.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWSubstitutionControls

open CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyWTypes ContextualSmallFamilyWSubstitution
open ContextualGraphDiagrams ContextualRealizedGraphs
open ConstructiveObservedMaterialControls
open ContextualGraphSmallWReadoutSubstitution

abbrev duplicated := ContextualSmallMapConstructions.coproduct params params

def forget : NaturalHom duplicated params where
  app _ := Sum.elim id id
  naturality _ receipt := by cases receipt <;> rfl

def leftPoint (stage : Nat) : duplicated.Elements := ⟨(task stage).1, .inl (task stage).2⟩
def rightPoint (stage : Nat) : duplicated.Elements := ⟨(task stage).1, .inr (task stage).2⟩

abbrev oldDomain := domain.native
abbrev oldBody := domain.bodyNative body
abbrev domainReading := ContextualGraphGeneratedWControls.domainReading
abbrev positionReading := ContextualGraphGeneratedWReadout.positionReading
  ContextualGraphGeneratedWControls.domainCode ContextualGraphGeneratedWControls.bodyCode
  ContextualGraphGeneratedWControls.bodyReading
abbrev newTrees := w (newDomain forget oldDomain) (newBody forget oldDomain oldBody)

def leftTree : newTrees.obj (leftPoint 2) :=
  wComparison forget oldDomain oldBody (leftPoint 2) (ContextualGraphGeneratedWControls.leaf 2 2 (by decide) (by decide))

def rightTree : newTrees.obj (rightPoint 2) :=
  wComparison forget oldDomain oldBody (rightPoint 2) (ContextualGraphGeneratedWControls.leaf 2 2 (by decide) (by decide))

theorem parameter_occurrences_distinct : (leftPoint 2).2 ≠ (rightPoint 2).2 := by
  intro same
  cases same

theorem parameter_map_is_noninjective : ¬ Function.Injective (forget.app (task 2).1) := by
  intro injective
  exact parameter_occurrences_distinct (injective (show forget.app (task 2).1 (leftPoint 2).2 =
    forget.app (task 2).1 (rightPoint 2).2 from rfl))

theorem full_receipts_remain_distinct :
    (⟨(leftPoint 2).2, leftTree⟩ : (total newTrees).obj (task 2).1) ≠
      ⟨(rightPoint 2).2, rightTree⟩ :=
  fun same => parameter_occurrences_distinct (congrArg Sigma.fst same)

def material_trees_match :
    Equal ((rebuilt forget oldDomain oldBody domainReading positionReading).read.app (task 2).1
      ⟨(leftPoint 2).2, leftTree⟩)
      ((rebuilt forget oldDomain oldBody domainReading positionReading).read.app (task 2).1
        ⟨(rightPoint 2).2, rightTree⟩) :=
  (forwardComparison forget oldDomain oldBody domainReading positionReading (leftPoint 2)
    (ContextualGraphGeneratedWControls.leaf 2 2 (by decide) (by decide))).symm.trans
      (forwardComparison forget oldDomain oldBody domainReading positionReading (rightPoint 2)
        (ContextualGraphGeneratedWControls.leaf 2 2 (by decide) (by decide)))

def material_carriers_match :
    Equal ((rebuiltParent forget oldDomain oldBody domainReading positionReading).app (task 2).1 (leftPoint 2).2)
      ((rebuiltParent forget oldDomain oldBody domainReading positionReading).app (task 2).1 (rightPoint 2).2) :=
  (carrierComparison forget oldDomain oldBody domainReading positionReading (leftPoint 2)).symm.trans
    (carrierComparison forget oldDomain oldBody domainReading positionReading (rightPoint 2))

theorem substituted_family_varies : ¬ Nonempty (newTrees.obj (leftPoint 0)) ∧ Nonempty (newTrees.obj (leftPoint 2)) := by
  refine ⟨?_, ⟨leftTree⟩⟩
  rintro ⟨tree⟩
  exact initial_W_empty ⟨(wComparison forget oldDomain oldBody (leftPoint 0)).symm tree⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWSubstitutionControls
