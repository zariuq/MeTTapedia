import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalOccurrenceAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesLeafClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryPlanOccurrenceAvailability
import Mettapedia.GSLT.LanguageDef.CostStaticPlanFVarSelection

/-!
# Positional support regimes for matched rho frames

Canonical occurrence ancestry ends at an exact finite plan position.  When
that position is intercepted by a stopped plan view, the plan occurrence's
availability is the certified target support of that boundary.  This module
connects those two facts without looking up a boundary by name, so repeated
equal boundary values remain distinct.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- Casting an occurrence across a root equality and immediately back leaves
the positional token unchanged. -/
@[simp]
theorem castCostStaticFVarOccurrenceRoot_symm_apply
    {leftRoot rightRoot : Pattern} (rootEq : leftRoot = rightRoot)
    (occurrence : CostStaticFVarOccurrence leftRoot) :
    castCostStaticFVarOccurrenceRoot rootEq.symm
        (castCostStaticFVarOccurrenceRoot rootEq occurrence) = occurrence := by
  cases rootEq
  rfl

@[simp]
theorem castCostStaticFVarOccurrenceRoot_trans
    {firstRoot secondRoot thirdRoot : Pattern}
    (firstEq : firstRoot = secondRoot)
    (secondEq : secondRoot = thirdRoot)
    (occurrence : CostStaticFVarOccurrence firstRoot) :
    castCostStaticFVarOccurrenceRoot secondEq
        (castCostStaticFVarOccurrenceRoot firstEq occurrence) =
      castCostStaticFVarOccurrenceRoot (firstEq.trans secondEq) occurrence := by
  subst secondRoot
  subst thirdRoot
  rfl

namespace CostStaticPlanStopped

/-- Root transport commutes with the positional stopped-boundary occurrence.
No name lookup or reconstruction is performed. -/
@[simp]
theorem boundaryOccurrence_castRoot
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload leftRoot rightRoot : Pattern}
    (rootEq : leftRoot = rightRoot)
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftRoot) :
    (state.castRoot rootEq).boundaryOccurrence =
      castCostStaticFVarOccurrenceRoot rootEq state.boundaryOccurrence := by
  subst rightRoot
  rfl

/-- A stopped context view tied to an exact free-variable occurrence returns
that same positional occurrence.  Both the selected name and its zipper are
read from the view; no boundary-table lookup by name is involved. -/
theorem boundaryOccurrence_eq_of_fvarContextInventoryView
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    {plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType}
    {occurrence : CostStaticFVarOccurrence plan.abstractPattern}
    (view : CostStaticPlanFVarContextInventoryView plan occurrence)
    (stopped : CostStaticPlanStopped rhoCIGSLT color targetFree view.rawPayload
      plan.abstractPattern)
    (viewEq : view.inventory.view = .stopped stopped) :
    stopped.boundaryOccurrence = occurrence := by
  apply CostStaticFVarOccurrence.ext
  · have selectedEq := view.selected_eq
    rw [viewEq] at selectedEq
    exact Pattern.fvar.inj selectedEq
  · have contextEq := view.context_eq
    rw [viewEq] at contextEq
    exact contextEq

/-- Node-level form of
`boundaryOccurrence_eq_of_fvarContextInventoryView`: after transporting the
stopped occurrence back to the decorated plan root, it is exactly the
executable inventory occurrence that selected the view. -/
theorem boundaryOccurrence_cast_eq_of_fvarContextInventoryView
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence)
    (view : CostStaticPlanFVarContextInventoryView node.plan
      (castCostStaticFVarOccurrenceRoot node.plan.decoration_abstractPattern
        (planDecorationOccurrenceAt node inventory position)))
    (stopped : CostStaticPlanStopped rhoCIGSLT color targetFree view.rawPayload
      node.plan.abstractPattern)
    (viewEq : view.inventory.view = .stopped stopped) :
    castCostStaticFVarOccurrenceRoot
        node.plan.decoration_abstractPattern.symm stopped.boundaryOccurrence =
      planDecorationOccurrenceAt node inventory position := by
  rw [boundaryOccurrence_eq_of_fvarContextInventoryView view stopped viewEq]
  exact castCostStaticFVarOccurrenceRoot_symm_apply
    node.plan.decoration_abstractPattern _

/-- An exact stopped boundary occurrence inherits the quote-local
availability of the finite plan position that selected it.

The occurrence equality is intentionally stronger than equality of names or
contexts.  It prevents a proof for one duplicate boundary occurrence from
being reused at another occurrence with the same printed name. -/
theorem targetSupport_eq_rhoCanonicalOccurrenceAvailable_of_boundaryOccurrence_eq
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload : Pattern}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence)
    (stopped : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.plan.abstractPattern)
    (occurrenceEq : castCostStaticFVarOccurrenceRoot
        node.plan.decoration_abstractPattern.symm stopped.boundaryOccurrence =
      planDecorationOccurrenceAt node inventory position) :
    stopped.certified.typed.boundary.targetSupport =
      rhoCanonicalOccurrenceAvailable node.targetBound
        (planDecorationOccurrenceAt node inventory position).context := by
  let positional := planDecorationOccurrenceAt node inventory position
  obtain ⟨packed⟩ := nonempty_planOccurrenceAt node inventory position
  let planAvailable := packed.1
  let occurrence := packed.2.1
  have nameEq : positional.name =
      costRegionBoundaryVariableName stopped.certified.typed.boundary := by
    have exactName := congrArg CostStaticFVarOccurrence.name occurrenceEq
    simpa [positional] using exactName.symm
  have planFree : WellSorted.ReflectiveSubstitutionBinderFree
      node.plan.abstractPattern = true :=
    CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base node.plan
      ⟨node.sourceSort.1, rfl⟩
  have availableEqSupport : planAvailable =
      stopped.certified.typed.boundary.targetSupport :=
    CostStaticRegionPlan.abstractOccurrence_available_eq_boundarySupport
      node.plan occurrence stopped.certified.typed.boundary nameEq
  have availableEqContext : planAvailable =
      rhoCanonicalOccurrenceAvailable node.targetBound positional.context :=
    CostStaticRegionPlan.abstractOccurrence_available_eq_quoteLocal
      node.plan planFree occurrence
  exact availableEqSupport.symm.trans availableEqContext

/-- Two exact stopped boundary occurrences inherit the three support regimes
proved for their paired canonical descendants: equal target support, sealed
left, or sealed right.

The ambient list is required to be the actual target binder context of both
nodes.  Keeping those equations explicit prevents an arbitrary caller list
from being mistaken for planner availability. -/
theorem targetSupports_eq_or_sealed_of_alignment
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload : Pattern}
    {leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    {leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory}
    {rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory}
    {leftTarget : CostStaticFVarOccurrence
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt leftNode
          leftEnvironment)
        rhoReflectivePresentation leftNode.targetBound.length 0
        (leftNode.reifiedSourceFrame leftEnvironment).1)}
    {rightTarget : CostStaticFVarOccurrence
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightNode
          rightEnvironment)
        rhoReflectivePresentation rightNode.targetBound.length 0
        (rightNode.reifiedSourceFrame rightEnvironment).1)}
    {ambient : List TypeExpr}
    (left : RhoCanonicalInventoryOccurrenceAlignmentCertificate leftNode
      leftEnvironment leftTarget ambient)
    (right : RhoCanonicalInventoryOccurrenceAlignmentCertificate rightNode
      rightEnvironment rightTarget ambient)
    (leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
      leftPayload leftNode.plan.abstractPattern)
    (rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
      rightPayload rightNode.plan.abstractPattern)
    (leftOccurrenceEq : castCostStaticFVarOccurrenceRoot
        leftNode.plan.decoration_abstractPattern.symm
          leftStopped.boundaryOccurrence =
      planDecorationOccurrenceAt leftNode leftInventory left.sourcePosition)
    (rightOccurrenceEq : castCostStaticFVarOccurrenceRoot
        rightNode.plan.decoration_abstractPattern.symm
          rightStopped.boundaryOccurrence =
      planDecorationOccurrenceAt rightNode rightInventory
        right.sourcePosition)
    (leftAmbientEq : ambient = leftNode.targetBound)
    (rightAmbientEq : ambient = rightNode.targetBound)
    (targetAvailableEq :
      rhoCanonicalOccurrenceAvailable ambient leftTarget.context =
        rhoCanonicalOccurrenceAvailable ambient rightTarget.context) :
    leftStopped.certified.typed.boundary.targetSupport =
        rightStopped.certified.typed.boundary.targetSupport ∨
      leftStopped.certified.typed.boundary.targetSupport = [] ∨
      rightStopped.certified.typed.boundary.targetSupport = [] := by
  have leftSupport :=
    targetSupport_eq_rhoCanonicalOccurrenceAvailable_of_boundaryOccurrence_eq
      leftNode leftInventory left.sourcePosition leftStopped leftOccurrenceEq
  have rightSupport :=
    targetSupport_eq_rhoCanonicalOccurrenceAvailable_of_boundaryOccurrence_eq
      rightNode rightInventory right.sourcePosition rightStopped
        rightOccurrenceEq
  have sourceCases := left.sourceAvailabilities_eq_or_sealed right
    targetAvailableEq
  have leftSupportAtAmbient :
      leftStopped.certified.typed.boundary.targetSupport =
        rhoCanonicalOccurrenceAvailable ambient
          (planDecorationOccurrenceAt leftNode leftInventory
            left.sourcePosition).context :=
    leftSupport.trans (congrArg
      (fun available => rhoCanonicalOccurrenceAvailable available
        (planDecorationOccurrenceAt leftNode leftInventory
          left.sourcePosition).context)
      leftAmbientEq.symm)
  have rightSupportAtAmbient :
      rightStopped.certified.typed.boundary.targetSupport =
        rhoCanonicalOccurrenceAvailable ambient
          (planDecorationOccurrenceAt rightNode rightInventory
            right.sourcePosition).context :=
    rightSupport.trans (congrArg
      (fun available => rhoCanonicalOccurrenceAvailable available
        (planDecorationOccurrenceAt rightNode rightInventory
          right.sourcePosition).context)
      rightAmbientEq.symm)
  rcases sourceCases with equal | leftSealed | rightSealed
  · exact Or.inl
      (leftSupportAtAmbient.trans (equal.trans rightSupportAtAmbient.symm))
  · exact Or.inr (Or.inl (leftSupportAtAmbient.trans leftSealed))
  · exact Or.inr (Or.inr (rightSupportAtAmbient.trans rightSealed))

end CostStaticPlanStopped

namespace CostStaticRegionNode

/-- Reindex one executable inventory position from the decorated plan root to
the undecorated abstract root used by total plan-selection inversion. -/
def planAbstractOccurrenceAt
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence) :
    CostStaticFVarOccurrence node.plan.abstractPattern :=
  castCostStaticFVarOccurrenceRoot node.plan.decoration_abstractPattern
    (planDecorationOccurrenceAt node inventory position)

@[simp]
theorem planAbstractOccurrenceAt_name
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence) :
    (planAbstractOccurrenceAt node inventory position).name =
      (planDecorationOccurrenceAt node inventory position).name :=
  castCostStaticFVarOccurrenceRoot_name _ _

@[simp]
theorem planAbstractOccurrenceAt_context
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence) :
    (planAbstractOccurrenceAt node inventory position).context =
      (planDecorationOccurrenceAt node inventory position).context :=
  castCostStaticFVarOccurrenceRoot_context _ _

/-- Every executable inventory position has a total reached-or-stopped plan
view tied to its exact occurrence. -/
theorem nonempty_planFVarContextInventoryViewAt
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence) :
    Nonempty (CostStaticPlanFVarContextInventoryView node.plan
      (planAbstractOccurrenceAt node inventory position)) :=
  node.plan.nonempty_fvarContextInventoryView _

/-- Reindexing a stopped view to the node's authored skeleton recovers the
exact executable inventory occurrence that selected it.  This is the bridge
needed by semantic environments, whose occurrence root is the authored
skeleton rather than the propositionally equal plan abstraction. -/
theorem stoppedBoundaryOccurrence_eq_inventory_of_fvarContextInventoryView
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence)
    (view : CostStaticPlanFVarContextInventoryView node.plan
      (planAbstractOccurrenceAt node inventory position))
    (stopped : CostStaticPlanStopped rhoCIGSLT color targetFree view.rawPayload
      node.plan.abstractPattern)
    (viewEq : view.inventory.view = .stopped stopped) :
    (stopped.castRoot node.skeleton_pattern.symm).boundaryOccurrence =
      (inventory.occurrenceAt position).fvarOccurrence := by
  have stoppedEq :=
    CostStaticPlanStopped.boundaryOccurrence_eq_of_fvarContextInventoryView
      view stopped viewEq
  apply CostStaticFVarOccurrence.ext
  · simpa [CostStaticPlanStopped.boundaryOccurrence_castRoot,
      planAbstractOccurrenceAt, planDecorationOccurrenceAt] using
        congrArg CostStaticFVarOccurrence.name stoppedEq
  · simpa [CostStaticPlanStopped.boundaryOccurrence_castRoot,
      planAbstractOccurrenceAt, planDecorationOccurrenceAt] using
        congrArg CostStaticFVarOccurrence.context stoppedEq

end CostStaticRegionNode

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
