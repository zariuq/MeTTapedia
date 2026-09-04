import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

/-!
# Foreign-declaration support-mismatch canary

The wrapped declaration removes one wrapped Quote/Drop shell.  Both endpoint
trees nevertheless have base-colour static roots.  On the left the removed
shell is one exposed foreign boundary; on the right the surviving base Quote
seals the corresponding foreign boundary.  This tests the exact combination
of foreign canonical equality, a common view colour, and unequal planner
supports.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignSupportMismatchCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def nameType : TypeExpr := .base (costBaseSortName "Name")
def processType : TypeExpr := .base (costBaseSortName "Proc")
def available : List TypeExpr := [nameType]

def declaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl

def foreignValue : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PZero") []]

def sealedFrame : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop") [foreignValue]]

def selectedShell : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [sealedFrame]]

def leftPattern : Pattern :=
  .apply (costBaseConstructorName "PDrop") [selectedShell]

def rightPattern : Pattern :=
  .apply (costBaseConstructorName "PDrop") [sealedFrame]

theorem leftWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available processType leftPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [leftPattern, selectedShell, sealedFrame, foreignValue, binderSafeAt,
    binderSafeListAt]

theorem rightWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available processType rightPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [rightPattern, sealedFrame, foreignValue, binderSafeAt,
    binderSafeListAt]

theorem canonical_eq :
    canonicalize declaration leftPattern =
      canonicalize declaration rightPattern := by
  decide

noncomputable def leftTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty available [] leftPattern
      processType :=
  (CostRegionTree.build? available [] leftPattern processType).get
    (CostRegionTree.build?_isSome_of_wellSorted leftWellSorted)

noncomputable def rightTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty available [] rightPattern
      processType :=
  (CostRegionTree.build? available [] rightPattern processType).get
    (CostRegionTree.build?_isSome_of_wellSorted rightWellSorted)

theorem leftTree_rootIsStatic : leftTree.rootIsStatic = true := by decide
theorem rightTree_rootIsStatic : rightTree.rootIsStatic = true := by decide

noncomputable def leftViewPair : Σ color, leftTree.StaticRootView color :=
  leftTree.staticRootView_of_rootIsStatic leftTree_rootIsStatic

noncomputable def rightViewPair : Σ color, rightTree.StaticRootView color :=
  rightTree.staticRootView_of_rootIsStatic rightTree_rootIsStatic

theorem leftViewPair_color : leftViewPair.1 = .base := by decide
theorem rightViewPair_color : rightViewPair.1 = .base := by decide

theorem left_entries_support :
    leftViewPair.2.node.finiteBoundaryTable.entries.map
        (·.boundary.targetSupport) = [available] := by
  decide

theorem right_entries_support :
    rightViewPair.2.node.finiteBoundaryTable.entries.map
        (·.boundary.targetSupport) = [[]] := by
  decide

theorem leftEntries_length :
    leftViewPair.2.node.finiteBoundaryTable.entries.length = 1 := by
  decide

theorem rightEntries_length :
    rightViewPair.2.node.finiteBoundaryTable.entries.length = 1 := by
  decide

noncomputable def leftBoundary :=
  leftViewPair.2.node.finiteBoundaryTable.entries[0]'(by
    rw [leftEntries_length]
    decide)

noncomputable def rightBoundary :=
  rightViewPair.2.node.finiteBoundaryTable.entries[0]'(by
    rw [rightEntries_length]
    decide)

noncomputable def leftBoundaryName : String :=
  costRegionBoundaryVariableName leftBoundary.boundary

noncomputable def rightBoundaryName : String :=
  costRegionBoundaryVariableName rightBoundary.boundary

theorem leftSkeleton_shape :
    leftViewPair.2.node.skeleton.1 =
      .apply "PDrop" [.fvar leftBoundaryName] := by
  rfl

theorem rightSkeleton_shape :
    rightViewPair.2.node.skeleton.1 =
      .apply "PDrop"
        [.apply "NQuote" [.apply "PDrop" [.fvar rightBoundaryName]]] := by
  rfl

noncomputable def leftEnvironment :=
  CostStaticAtomEnvironment.ofInventory
    (leftViewPair.2.node.semanticAtomEnvironment
      (leftViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

noncomputable def rightEnvironment :=
  CostStaticAtomEnvironment.ofInventory
    (rightViewPair.2.node.semanticAtomEnvironment
      (rightViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

noncomputable def leftOccurrence :
    CostStaticFVarOccurrence leftViewPair.2.node.skeleton.1 where
  name := leftBoundaryName
  context := .apply "PDrop" [] .hole []
  selected := by
    rw [leftSkeleton_shape]
    exact .apply .here

noncomputable def rightOccurrence :
    CostStaticFVarOccurrence rightViewPair.2.node.skeleton.1 where
  name := rightBoundaryName
  context := .apply "PDrop" []
    (.apply "NQuote" [] (.apply "PDrop" [] .hole []) []) []
  selected := by
    rw [rightSkeleton_shape]
    exact .apply (.apply (.apply .here))

theorem leftSlot_exists :
    (leftEnvironment.slotOfName? leftBoundaryName).isSome = true :=
  leftEnvironment.slotOfName?_isSome_of_occurrence leftOccurrence

theorem rightSlot_exists :
    (rightEnvironment.slotOfName? rightBoundaryName).isSome = true :=
  rightEnvironment.slotOfName?_isSome_of_occurrence rightOccurrence

noncomputable def leftSlot : Fin leftEnvironment.atomCount :=
  (leftEnvironment.slotOfName? leftBoundaryName).get leftSlot_exists

noncomputable def rightSlot : Fin rightEnvironment.atomCount :=
  (rightEnvironment.slotOfName? rightBoundaryName).get rightSlot_exists

theorem leftSlot_selected :
    leftEnvironment.slotOfName? leftBoundaryName = some leftSlot :=
  (Option.some_get leftSlot_exists).symm

theorem rightSlot_selected :
    rightEnvironment.slotOfName? rightBoundaryName = some rightSlot :=
  (Option.some_get rightSlot_exists).symm

theorem leftBoundary_mem :
    leftBoundary ∈ leftViewPair.2.node.boundaryTable.entries := by
  unfold leftBoundary
  exact List.get_mem _ _

theorem rightBoundary_mem :
    rightBoundary ∈ rightViewPair.2.node.boundaryTable.entries := by
  unfold rightBoundary
  exact List.get_mem _ _

theorem leftBoundary_support :
    leftBoundary.boundary.targetSupport = available := by
  decide

theorem rightBoundary_support :
    rightBoundary.boundary.targetSupport = [] := by
  decide

theorem atom_keys_ne :
    (leftEnvironment.atomValue leftSlot).key ≠
      (rightEnvironment.atomValue rightSlot).key := by
  have leftSupport :
      (leftEnvironment.atomValue leftSlot).key.targetSupport = available := by
    calc
      (leftEnvironment.atomValue leftSlot).key.targetSupport =
          leftViewPair.2.node.boundaryTable.sourceSupport
            leftOccurrence.name :=
        leftEnvironment.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
          leftOccurrence leftSlot leftSlot_selected
      _ = leftViewPair.2.node.boundaryTable.sourceSupport
          (costRegionBoundaryVariableName leftBoundary.boundary) := by
        rfl
      _ = leftBoundary.boundary.targetSupport :=
        leftViewPair.2.node.boundaryTable.sourceSupport_boundaryVariable
          leftBoundary leftBoundary_mem
      _ = available := leftBoundary_support
  have rightSupport :
      (rightEnvironment.atomValue rightSlot).key.targetSupport = [] := by
    calc
      (rightEnvironment.atomValue rightSlot).key.targetSupport =
          rightViewPair.2.node.boundaryTable.sourceSupport
            rightOccurrence.name :=
        rightEnvironment.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
          rightOccurrence rightSlot rightSlot_selected
      _ = rightViewPair.2.node.boundaryTable.sourceSupport
          (costRegionBoundaryVariableName rightBoundary.boundary) := by
        rfl
      _ = rightBoundary.boundary.targetSupport :=
        rightViewPair.2.node.boundaryTable.sourceSupport_boundaryVariable
          rightBoundary rightBoundary_mem
      _ = [] := rightBoundary_support
  intro keysEq
  have supportsEq := congrArg CostStaticAtomKey.targetSupport keysEq
  rw [leftSupport, rightSupport] at supportsEq
  exact absurd supportsEq (by decide)

theorem rootsAligned : CanonicalRootAligned declaration leftPattern
    rightPattern := by
  apply CanonicalRootAligned.apply (by decide)
  exact .cons (by decide) .nil

theorem color_is_foreign : (.base : CostStaticColor) ≠ .wrapped := by decide

noncomputable def leftBaseView : leftTree.StaticRootView .base :=
  leftViewPair_color ▸ leftViewPair.2

noncomputable def rightBaseView : rightTree.StaticRootView .base :=
  rightViewPair_color ▸ rightViewPair.2

theorem leftBaseView_skeleton :
    leftBaseView.node.skeleton.1 =
      .apply "PDrop" [.fvar leftBoundaryName] := by
  simpa [leftBaseView] using leftSkeleton_shape

theorem rightBaseView_skeleton :
    rightBaseView.node.skeleton.1 =
      .apply "PDrop"
        [.apply "NQuote" [.apply "PDrop" [.fvar rightBoundaryName]]] := by
  simpa [rightBaseView] using rightSkeleton_shape

noncomputable def planAlignment :
    CanonicalStopAligned rhoReflectivePresentation
      (CostStaticPlanCanonicalStop leftBaseView.node.plan
        rightBaseView.node.plan rhoReflectivePresentation declaration
        (RhoCanonicalRawStop .wrapped
          (sizeOf leftPattern + sizeOf rightPattern)))
      leftBaseView.node.skeleton.1 rightBaseView.node.skeleton.1 := by
  apply leftBaseView.node.sourceCanonicalStopAligned_of_rawAlignment
    rho_collectionChoiceDeterministic rhoReflectivePresentation declaration
    rightBaseView.node (leftBaseView.targetBound_eq_targetBound rightBaseView)
    (leftBaseView.sourceSort_eq_sourceSort rightBaseView)
  rw [leftBaseView.patternEq, rightBaseView.patternEq]
  exact canonicalStopAligned_of_root_aligned declaration rootsAligned

theorem alignment_has_stop
    {stop : Pattern → Pattern → Prop}
    (aligned : CanonicalStopAligned rhoReflectivePresentation stop
      (.apply "PDrop" [.fvar leftBoundaryName])
      (.apply "PDrop"
        [.apply "NQuote" [.apply "PDrop" [.fvar rightBoundaryName]]])) :
    ∃ left right, stop left right := by
  cases aligned with
  | leaf given => exact ⟨_, _, given⟩
  | apply _ arguments =>
      cases arguments with
      | cons head _ =>
          cases head with
          | leaf given => exact ⟨_, _, given⟩

theorem planStop_exists :
    ∃ left right,
      CostStaticPlanCanonicalStop leftBaseView.node.plan
        rightBaseView.node.plan rhoReflectivePresentation declaration
        (RhoCanonicalRawStop .wrapped
          (sizeOf leftPattern + sizeOf rightPattern)) left right := by
  apply alignment_has_stop
  simpa only [leftBaseView_skeleton, rightBaseView_skeleton] using
    planAlignment

end ForeignSupportMismatchCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
