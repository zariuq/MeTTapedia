import Mettapedia.GSLT.LanguageDef.CostRestorationSourceVariable
import Mettapedia.GSLT.LanguageDef.CostStaticPlanFVarTerminal
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalOccurrenceAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesPositionalSupport

/-!
# Positional source-variable leaves of matched rho frames

Canonical occurrence ancestry identifies the exact authored occurrence behind
each final source-frame variable.  When both occurrences are the same authored
source variable, their endpoint semantic keys coincide and hence their common
reifications are literally equal.  This is the source/source terminal of the
matched static-frame recursion.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- Two final canonical occurrences whose exact plan ancestors are the same
authored source variable have a common-restoration apex.

The final canonical names may have been changed by atom reification and keyed
canonicalization.  They are therefore related to the authored names through
the two positional ancestry certificates, not by string equality. -/
noncomputable def sourceVariableCanonicalOccurrences_commonRestorationApex
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftTarget : CostStaticFVarOccurrence
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftNode leftEnvironment)
        rhoReflectivePresentation leftNode.targetBound.length 0
        (leftNode.reifiedSourceFrame leftEnvironment).1)}
    {rightTarget : CostStaticFVarOccurrence
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightNode rightEnvironment)
        rhoReflectivePresentation rightNode.targetBound.length 0
        (rightNode.reifiedSourceFrame rightEnvironment).1)}
    {ambient : List TypeExpr}
    (leftAlignment :
      RhoCanonicalInventoryOccurrenceAlignmentCertificate leftNode
        leftEnvironment leftTarget ambient)
    (rightAlignment :
      RhoCanonicalInventoryOccurrenceAlignmentCertificate rightNode
        rightEnvironment rightTarget ambient)
    (leftName rightName : String)
    (leftOrigin :
      (planAbstractOccurrenceAt leftNode leftInventory
        leftAlignment.sourcePosition).name =
          costRegionSourceVariableName leftName)
    (rightOrigin :
      (planAbstractOccurrenceAt rightNode rightInventory
        rightAlignment.sourcePosition).name =
          costRegionSourceVariableName rightName)
    (namesEq : leftName = rightName)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      declaration depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar leftTarget.name))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar rightTarget.name)) := by
  subst rightName
  have leftSourceOrigin : leftAlignment.sourceOccurrence.name =
      costRegionSourceVariableName leftName := by
    rw [← leftAlignment.position_eq]
    simpa using leftOrigin
  have rightSourceOrigin : rightAlignment.sourceOccurrence.name =
      costRegionSourceVariableName leftName := by
    rw [← rightAlignment.position_eq]
    simpa using rightOrigin
  obtain ⟨leftSlot, leftSelected⟩ :=
    Option.isSome_iff_exists.mp
      (leftEnvironment.slotOfName?_isSome_of_occurrence
        leftAlignment.sourceOccurrence)
  obtain ⟨rightSlot, rightSelected⟩ :=
    Option.isSome_iff_exists.mp
      (rightEnvironment.slotOfName?_isSome_of_occurrence
        rightAlignment.sourceOccurrence)
  have leftAtomName : leftEnvironment.atomName leftSlot = leftTarget.name := by
    calc
      leftEnvironment.atomName leftSlot =
          (leftEnvironment.reifyOccurrence
            leftAlignment.sourceOccurrence).name :=
        (leftEnvironment.reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
          leftAlignment.sourceOccurrence leftSlot leftSelected).symm
      _ = leftAlignment.reifiedOccurrence.name := by
        rw [leftAlignment.reified_eq]
      _ = leftTarget.name := leftAlignment.canonical_name_eq
  have rightAtomName : rightEnvironment.atomName rightSlot =
      rightTarget.name := by
    calc
      rightEnvironment.atomName rightSlot =
          (rightEnvironment.reifyOccurrence
            rightAlignment.sourceOccurrence).name :=
        (rightEnvironment.reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
          rightAlignment.sourceOccurrence rightSlot rightSelected).symm
      _ = rightAlignment.reifiedOccurrence.name := by
        rw [rightAlignment.reified_eq]
      _ = rightTarget.name := rightAlignment.canonical_name_eq
  let leaf := leftEnvironment.sourceVariable_commonRestorationApex
    rightEnvironment leftName leftAlignment.sourceOccurrence
      rightAlignment.sourceOccurrence leftSourceOrigin rightSourceOrigin
      leftSlot rightSlot leftSelected rightSelected declaration depth
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (congrArg
      (fun name =>
        (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
          leftEnvironment.lookupAtom?
          (leftEnvironment.semanticKeyCospan rightEnvironment).leftSlot
          (.fvar name)) leftAtomName)
    (congrArg
      (fun name =>
        (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
          rightEnvironment.lookupAtom?
          (leftEnvironment.semanticKeyCospan rightEnvironment).rightSlot
          (.fvar name)) rightAtomName)
    leaf

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
