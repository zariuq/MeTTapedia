import Mettapedia.GSLT.LanguageDef.CostStaticPlanSelection
import Mettapedia.GSLT.LanguageDef.CostElaborationDecoration

/-!
# Exact free-variable views of Cost static plans

Selection inversion for a static plan returns a reached or stopped context
view.  For a selected free-variable occurrence, this file packages the two
equalities saying that the view retains exactly the supplied zipper and leaf.
The package is positional: it never searches the boundary table by name.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open WellSorted

namespace CostStaticPlanStopped

/-- Transport a stopped plan view across equality of its complete abstract
root.  The retained boundary, payload factorization, and positional zipper are
unchanged; only the root index of `abstract_eq` is transported. -/
def castRoot
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload leftRoot rightRoot : Pattern}
    (rootEq : leftRoot = rightRoot)
    (state : CostStaticPlanStopped source color targetFree payload leftRoot) :
    CostStaticPlanStopped source color targetFree payload rightRoot := by
  subst rightRoot
  exact state

@[simp]
theorem castRoot_rfl
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload root : Pattern}
    (state : CostStaticPlanStopped source color targetFree payload root) :
    state.castRoot rfl = state := by
  rfl

@[simp]
theorem castRoot_trans
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {payload firstRoot secondRoot thirdRoot : Pattern}
    (firstEq : firstRoot = secondRoot)
    (secondEq : secondRoot = thirdRoot)
    (state : CostStaticPlanStopped source color targetFree payload firstRoot) :
    (state.castRoot firstEq).castRoot secondEq =
      state.castRoot (firstEq.trans secondEq) := by
  subst secondRoot
  subst thirdRoot
  rfl

@[simp]
theorem castRoot_certified_typed
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload leftRoot rightRoot : Pattern}
    (rootEq : leftRoot = rightRoot)
    (state : CostStaticPlanStopped source color targetFree payload leftRoot) :
    (state.castRoot rootEq).certified.typed = state.certified.typed := by
  subst rightRoot
  rfl

end CostStaticPlanStopped

/-- A total plan-selection view tied to one exact free-variable occurrence.
The raw payload may lie below a stopped boundary, so it remains existential
data rather than being reconstructed from the abstract leaf. -/
structure CostStaticPlanFVarContextInventoryView
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (occurrence : CostStaticFVarOccurrence plan.abstractPattern) : Type where
  rawPayload : Pattern
  inventory : CostStaticPlanContextInventoryView source color targetFree
    rawPayload plan.abstractPattern plan.boundaryTable.entries
  context_eq : inventory.view.abstractContext = occurrence.context
  selected_eq : inventory.view.selectedAbstract = .fvar occurrence.name

/-- Every exact free-variable occurrence in a plan abstraction has a
position-tied reached-or-stopped inventory view. -/
theorem CostStaticRegionPlan.nonempty_fvarContextInventoryView
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (occurrence : CostStaticFVarOccurrence plan.abstractPattern) :
    Nonempty (CostStaticPlanFVarContextInventoryView plan occurrence) := by
  obtain ⟨rawPayload, inventory, contextEq, selectedEq⟩ :=
    plan.exists_contextInventoryView_of_abstractSelection occurrence.selected
  exact ⟨
    { rawPayload := rawPayload
      inventory := inventory
      context_eq := contextEq
      selected_eq := selectedEq }⟩

namespace CostStaticPlanFVarContextInventoryView

/-- Reconstruct the selected occurrence directly from the returned view. -/
def selectedOccurrence
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    {plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType}
    {occurrence : CostStaticFVarOccurrence plan.abstractPattern}
    (view : CostStaticPlanFVarContextInventoryView plan occurrence) :
    CostStaticFVarOccurrence plan.abstractPattern where
  name := occurrence.name
  context := view.inventory.view.abstractContext
  selected := by
    simpa only [view.context_eq] using occurrence.selected

/-- Reconstructing the occurrence from a total view returns the original
positional token, including its zipper. -/
@[simp]
theorem selectedOccurrence_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    {plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType}
    {occurrence : CostStaticFVarOccurrence plan.abstractPattern}
    (view : CostStaticPlanFVarContextInventoryView plan occurrence) :
    view.selectedOccurrence = occurrence := by
  apply CostStaticFVarOccurrence.ext
  · rfl
  · exact view.context_eq

/-- A stopped total view supplies the exact singleton-to-parent table
embedding after any root transport of the stopped state.  The transport does
not alter the retained certified boundary or the embedding's keep/skip path. -/
def stoppedEntryEmbedding
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    {plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType}
    {occurrence : CostStaticFVarOccurrence plan.abstractPattern}
    (view : CostStaticPlanFVarContextInventoryView plan occurrence)
    (stopped : CostStaticPlanStopped source color targetFree view.rawPayload
      plan.abstractPattern)
    (viewEq : view.inventory.view = .stopped stopped)
    {root : Pattern} (rootEq : plan.abstractPattern = root) :
    CostStaticPlanEntryEmbedding source color targetFree
      [(stopped.castRoot rootEq).certified.typed]
      plan.boundaryTable.entries := by
  subst root
  have embedding := view.inventory.entryEmbedding
  rw [viewEq] at embedding
  simpa only [CostStaticPlanStopped.castRoot_certified_typed,
    CostStaticPlanContextView.retainedEntries] using embedding

end CostStaticPlanFVarContextInventoryView

end Mettapedia.GSLT.LanguageDef
