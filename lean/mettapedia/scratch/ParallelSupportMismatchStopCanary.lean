import ForeignSupportMismatchCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

/-!
# Parallel support-mismatch stop canary

Two foreign-canonically equal process cells expose the same static boundary
with different target supports.  Placing both cells in opposite orders under
the selected parallel collection tests whether the complete plan-stop
telescope rules out a depth-sensitive stable-tie permutation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelSupportMismatchStopCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ForeignSupportMismatchCanary

def selectedDeclaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl

def leftParallel : Pattern :=
  .collection selectedDeclaration.parallelCollection
    [leftPattern, rightPattern] none

def rightParallel : Pattern :=
  .collection selectedDeclaration.parallelCollection
    [rightPattern, leftPattern] none

theorem leftParallel_wellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available processType leftParallel := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [leftParallel, selectedDeclaration, leftPattern, rightPattern,
    selectedShell, sealedFrame, foreignValue, binderSafeAt,
    binderSafeListAt]

theorem rightParallel_wellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available processType rightParallel := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [rightParallel, selectedDeclaration, leftPattern, rightPattern,
    selectedShell, sealedFrame, foreignValue, binderSafeAt,
    binderSafeListAt]

theorem foreign_canonical_eq :
    canonicalize declaration leftParallel =
      canonicalize declaration rightParallel := by
  change canonicalize declaration
      (.collection declaration.parallelCollection
        [leftPattern, rightPattern] none) =
    canonicalize declaration
      (.collection declaration.parallelCollection
        [rightPattern, leftPattern] none)
  exact canonicalize_parallel_permutation declaration
    (List.Perm.swap leftPattern rightPattern []).symm

noncomputable def leftTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty available [] leftParallel
      processType :=
  (CostRegionTree.build? available [] leftParallel processType).get
    (CostRegionTree.build?_isSome_of_wellSorted leftParallel_wellSorted)

noncomputable def rightTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty available [] rightParallel
      processType :=
  (CostRegionTree.build? available [] rightParallel processType).get
    (CostRegionTree.build?_isSome_of_wellSorted rightParallel_wellSorted)

theorem leftTree_rootIsStatic : leftTree.rootIsStatic = true := by decide

theorem rightTree_rootIsStatic : rightTree.rootIsStatic = true := by decide

noncomputable def leftViewPair : Σ color, leftTree.StaticRootView color :=
  leftTree.staticRootView_of_rootIsStatic leftTree_rootIsStatic

noncomputable def rightViewPair : Σ color, rightTree.StaticRootView color :=
  rightTree.staticRootView_of_rootIsStatic rightTree_rootIsStatic

theorem leftViewPair_color : leftViewPair.1 = .base := by decide

theorem rightViewPair_color : rightViewPair.1 = .base := by decide

noncomputable def leftView : leftTree.StaticRootView .base :=
  leftViewPair_color ▸ leftViewPair.2

noncomputable def rightView : rightTree.StaticRootView .base :=
  rightViewPair_color ▸ rightViewPair.2

theorem leftView_rootClass :
    leftView.node.plan.rootClass =
      .collection rhoReflectivePresentation.parallelCollection := by
  rfl

theorem rightView_rootClass :
    rightView.node.plan.rootClass =
      .collection rhoReflectivePresentation.parallelCollection := by
  rfl

noncomputable def stopMeasure : Nat :=
  sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 + 1

theorem root_rawStop :
    RhoCanonicalRawStop .wrapped stopMeasure leftView.node.term.1
      rightView.node.term.1 := by
  refine ⟨⟨Or.inl ?_, ?_⟩, ?_⟩
  · exact Or.inr ⟨[leftPattern, rightPattern], by
      rw [leftView.patternEq]
      rfl⟩
  · rw [leftView.patternEq, rightView.patternEq]
    exact foreign_canonical_eq
  · simp [stopMeasure]

noncomputable def leftRootReached :
    CostStaticPlanReached rhoCIGSLT .base FreeTypeContext.empty
      leftView.node.term.1 leftView.node.plan.abstractPattern where
  sourceBound := leftView.node.sourceBound
  targetBound := leftView.node.targetBound
  thinning := leftView.node.thinning
  sourceAvailable := leftView.node.targetBound
  outer := .hole
  sourceType := .base leftView.node.sourceSort.1
  plan := leftView.node.plan
  skeletonContext := .hole
  abstract_eq := rfl

noncomputable def rightRootReached :
    CostStaticPlanReached rhoCIGSLT .base FreeTypeContext.empty
      rightView.node.term.1 rightView.node.plan.abstractPattern where
  sourceBound := rightView.node.sourceBound
  targetBound := rightView.node.targetBound
  thinning := rightView.node.thinning
  sourceAvailable := rightView.node.targetBound
  outer := .hole
  sourceType := .base rightView.node.sourceSort.1
  plan := rightView.node.plan
  skeletonContext := .hole
  abstract_eq := rfl

theorem root_stopAtPayload :
    CostStaticPlanCanonicalStopAtPayload leftView.node.plan
      rightView.node.plan rhoReflectivePresentation declaration
      (RhoCanonicalRawStop .wrapped stopMeasure)
      leftView.node.term.1 rightView.node.term.1
      leftView.node.plan.abstractPattern rightView.node.plan.abstractPattern := by
  have sameBound := leftView.targetBound_eq_targetBound rightView
  have sameSort := leftView.sourceSort_eq_sourceSort rightView
  refine ⟨leftRootReached, rightRootReached,
    leftView.node.planRawAdmission, rightView.node.planRawAdmission,
    rfl, rfl, ?_, ?_, ?_, sameBound, ?_, ?_, ?_, ?_, ?_, Or.inl root_rawStop,
    le_rfl, le_rfl, .leaf root_rawStop⟩
  · exact congrArg (fun sort => (.base sort.1 : TypeExpr)) sameSort
  · exact sameBound
  · exact congrArg
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base)
      sameBound
  · cases sameBound
    rfl
  · exact ⟨CostStaticPlanEntryEmbedding.refl _⟩
  · exact ⟨CostStaticPlanEntryEmbedding.refl _⟩
  · exact ⟨.refl⟩
  · exact ⟨.refl⟩

theorem root_planStop :
    CostStaticPlanCanonicalStop leftView.node.plan rightView.node.plan
      rhoReflectivePresentation declaration
      (RhoCanonicalRawStop .wrapped stopMeasure)
      leftView.node.plan.abstractPattern rightView.node.plan.abstractPattern :=
  ⟨leftView.node.term.1, rightView.node.term.1, root_stopAtPayload⟩

theorem left_entries_support :
    leftView.node.finiteBoundaryTable.entries.map
        (·.boundary.targetSupport) = [available, []] := by
  decide

theorem right_entries_support :
    rightView.node.finiteBoundaryTable.entries.map
        (·.boundary.targetSupport) = [[], available] := by
  decide

end ParallelSupportMismatchStopCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
