import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRestorationClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary

/-!
# Canary for restoration-level foreign-boundary closure

The breadth witness changes a wrapped parent from a certified foreign
boundary occurrence to a direct source-variable occurrence.  Their rigid
names and provenance differ, but both restore to the same free variable.
This module rebuilds the exact parent bridge through the generic
restoration-level congruence rather than the fixture's direct depth-zero
calculation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary

/-- Structural target of the stopped-boundary/source-variable child
alignment. -/
def rhoBreadthFvarAStructuralTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] (.fvar "a")
      (.base (costBaseSortName "Name")) :=
  .fvar (by rfl)

/-- The exact child selected by the stopped context view aligns with the
direct structural variable through the retained Quote/Drop semantic atom. -/
noncomputable def rhoBreadthStoppedChildToFvarAlignment :
    CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      (rhoPairStoppedView.selectedTreeFromForest
        rhoBreadthLeftProcessChildren ⟨0, by decide⟩)
      rhoBreadthFvarAStructuralTree := by
  refine .semanticAtom _ _ ?_
  exact rhoBreadthBaseRedexANodeSemanticAtomJoin.transport (by
      change (CostRegionTree.normalizeHereditary
          rhoBreadthBoundaryChildA).pattern =
        (CostStaticRegionNode.normalizeHereditary rhoBreadthBaseRedexANode
          (TypedCostRegionBoundaryTable.Values.original
            rhoBreadthBaseRedexANode.finiteBoundaryTable)).1
      exact rhoBreadthBoundaryChildA_normalizeHereditary.trans
        rhoBreadthBaseRedexANode_normalizeHereditary.symm) (by
      change (rhoBreadthFvarAStructuralTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        .fvar "a"
      simp [rhoBreadthFvarAStructuralTree, CostRegionTree.normalize])

/-- The breadth fixture inhabits the reusable stopped-boundary/source-variable
root certificate with a genuine recursive child alignment. -/
noncomputable def rhoBreadthStoppedToSourceVariableCertificate :
    RhoStoppedBoundarySourceVariableRootCertificate
      rhoBreadthLeftProcessNode rhoBreadthRightProcessNode
      rhoBreadthLeftProcessChildren rhoBreadthRightProcessChildren
      rhoPairStoppedView ⟨0, by decide⟩ := by
  let leftEnvironment := rhoBreadthLeftProcessNode.normalizationEnvironment
    rhoHereditaryStaticNormalizer rhoBreadthLeftProcessChildren
  let rightEnvironment := rhoBreadthRightProcessNode.normalizationEnvironment
    rhoHereditaryStaticNormalizer rhoBreadthRightProcessChildren
  have leftMembership : costRegionBoundaryVariableName
      rhoBreadthBoundaryWitnessA.typed.boundary ∈
        rhoBreadthLeftProcessNode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthLeftProcessNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  let leftOccurrenceExists :=
    rhoBreadthLeftProcessNode.skeleton_fvar_covered _ leftMembership
  let leftOccurrence := Classical.choose leftOccurrenceExists
  have leftOccurrenceName := Classical.choose_spec leftOccurrenceExists
  let leftSlotExists := Option.isSome_iff_exists.mp
    (leftEnvironment.slotOfName?_isSome_of_occurrence leftOccurrence)
  let leftSlot := Classical.choose leftSlotExists
  have leftSelectedAtOccurrence := Classical.choose_spec leftSlotExists
  have leftSelected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName
        rhoBreadthBoundaryWitnessA.typed.boundary) = some leftSlot := by
    rw [← leftOccurrenceName]
    exact leftSelectedAtOccurrence
  have rightMembership : costRegionSourceVariableName "a" ∈
      rhoBreadthRightProcessNode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthRightProcessNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  let rightOccurrenceExists :=
    rhoBreadthRightProcessNode.skeleton_fvar_covered _ rightMembership
  let rightOccurrence := Classical.choose rightOccurrenceExists
  have rightOccurrenceName := Classical.choose_spec rightOccurrenceExists
  let rightSlotExists := Option.isSome_iff_exists.mp
    (rightEnvironment.slotOfName?_isSome_of_occurrence rightOccurrence)
  let rightSlot := Classical.choose rightSlotExists
  have rightSelectedAtOccurrence := Classical.choose_spec rightSlotExists
  have rightSelected : rightEnvironment.slotOfName?
      (costRegionSourceVariableName "a") = some rightSlot := by
    rw [← rightOccurrenceName]
    exact rightSelectedAtOccurrence
  have leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
      (rhoPairStoppedView.view.retainedEntries.get
        ⟨0, by decide⟩).boundary := by
    exact leftOccurrenceName
  have canonicalFramesAligned : FvarAligned
      (fun leftName rightName =>
        leftName = leftEnvironment.atomName leftSlot ∧
          rightName = rightEnvironment.atomName rightSlot)
      (rhoBreadthLeftProcessNode.canonicalizeReifiedTargetFrame leftEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation))
      (rhoBreadthRightProcessNode.canonicalizeReifiedTargetFrame
        rightEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation)) := by
    have leftFrame := rhoBreadthProcess_canonicalFrame
      rhoBreadthLeftProcessNode leftEnvironment _ leftSlot leftSelected
      rhoBreadthLeftProcessNode_skeleton_pattern rfl
    have rightFrame := rhoBreadthProcess_canonicalFrame
      rhoBreadthRightProcessNode rightEnvironment _ rightSlot rightSelected
      rhoBreadthRightProcessNode_skeleton_pattern rfl
    rw [leftFrame, rightFrame]
    exact .apply _ (.cons (.fvar ⟨rfl, rfl⟩) .nil)
  refine
    { sameDepth := rfl
      leftOccurrence := leftOccurrence
      leftNameEq := leftNameEq
      rightOccurrence := rightOccurrence
      name := "a"
      rightNameEq := rightOccurrenceName
      leftSlot := leftSlot
      leftSelected := leftSelectedAtOccurrence
      rightSlot := rightSlot
      rightSelected := rightSelectedAtOccurrence
      rightAvailable := []
      rightOuter := []
      rightType := .base (costBaseSortName "Name")
      rightTree := rhoBreadthFvarAStructuralTree
      childAlignment := rhoBreadthStoppedChildToFvarAlignment
      rightNormal := by
        simp [rhoBreadthFvarAStructuralTree, CostRegionTree.normalize]
      canonicalFramesAligned := canonicalFramesAligned }

/-- The breadth process-root bridge reconstructed through structural
canonical-frame alignment plus atomwise restoration at every binder depth. -/
noncomputable def rhoBreadthProcessRootBridge_viaRestoredFvarAlignment :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      rhoBreadthLeftProcessTree rhoBreadthRightProcessTree :=
  rhoBreadthStoppedToSourceVariableCertificate.toRootBridge

/-- The generic restoration closure gives the same exact executor equality
as the original hand-built breadth bridge. -/
theorem rhoBreadth_process_normalize_eq_viaRestoredFvarAlignment :
    (rhoBreadthLeftProcessTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoBreadthRightProcessTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  rhoBreadthProcessRootBridge_viaRestoredFvarAlignment.toTreeAlignment.normalize_pattern_eq

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
