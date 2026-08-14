import Mettapedia.GSLT.LanguageDef.CostStaticPlanFVarSelection

/-!
# Terminal classification of selected static-plan variables

A free-variable occurrence in a static-plan abstraction has exactly two
semantic origins.  It is either an authored source variable, or the rigid
name of a certified foreign boundary.  This file packages that dichotomy
without identifying occurrences that happen to share a name.

The input selection view may stop at a boundary or may reach the boundary
plan itself.  The latter representation is normalized to the former, so
downstream proofs need only the two semantic terminal cases.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open WellSorted

/-- Plan-local origin of an abstract free-variable leaf.  This classification
does not mention a zipper or table embedding; those proof-relevant indices are
transported only after the plan shape has been inverted. -/
inductive CostStaticRegionPlanFVarOrigin
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (selectedName : String) : Type where
  | sourceVariable (name : String)
      (name_eq : selectedName = costRegionSourceVariableName name)
      (pattern_eq : pattern = .fvar name)
      (lookup : targetFree name =
        some (mapTypeExpr (color.symbols source) sourceType))
  | boundary
      {boundarySupport : List TypeExpr} {boundaryType : TypeExpr}
      {content : Pattern}
      (certified : CertifiedCostRegionBoundary source color targetFree
        boundarySupport boundaryType content)
      (certifies : certifyCostRegionBoundary? source color targetFree
        boundarySupport boundaryType content = some certified)
      (content_eq : content = pattern)
      (abstract_eq : plan.abstractPattern =
        .fvar (costRegionBoundaryVariableName certified.typed.boundary))
      (entries_eq : plan.boundaryTable.entries = [certified.typed])

namespace CostStaticRegionPlanFVarOrigin

/-- Invert an abstract free-variable equation before introducing occurrence
or zipper indices. -/
def ofAbstractFVar
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (selectedName : String)
    (selected : plan.abstractPattern = .fvar selectedName) :
    CostStaticRegionPlanFVarOrigin plan selectedName := by
  cases plan with
  | bvar sourceIndex lookup correspondence availableScope =>
      simp [CostStaticRegionPlan.abstractPattern] at selected
  | fvar lookup =>
      simp only [CostStaticRegionPlan.abstractPattern, Pattern.fvar.injEq]
        at selected
      exact .sourceVariable _ selected.symm rfl lookup
  | boundaryApplication constructor rendered outsideCurrent certified
      certifies =>
      exact .boundary certified certifies rfl rfl rfl
  | application constructor rendered current preimage notBare children =>
      simp [CostStaticRegionPlan.abstractPattern] at selected
  | lambda bodyPlan =>
      simp [CostStaticRegionPlan.abstractPattern] at selected
  | multiLambda bodyPlan =>
      simp [CostStaticRegionPlan.abstractPattern] at selected
  | collection choice chosen children =>
      simp [CostStaticRegionPlan.abstractPattern] at selected
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact .boundary certified certifies rfl rfl rfl

end CostStaticRegionPlanFVarOrigin

/-- Semantic origin of one exact free-variable occurrence in a static-plan
abstraction.  The source case retains the authored name.  The boundary case
retains a stopped positional view and hence the exact certified table entry.
-/
inductive CostStaticPlanFVarTerminal
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
  (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (occurrence : CostStaticFVarOccurrence plan.abstractPattern) : Type where
  | sourceVariable
      (view : CostStaticPlanFVarContextInventoryView plan occurrence)
      (reached : CostStaticPlanReached source color targetFree view.rawPayload
        plan.abstractPattern)
      (view_eq : view.inventory.view = .reached reached)
      (name : String)
      (name_eq : occurrence.name = costRegionSourceVariableName name)
      (payload_eq : view.rawPayload = .fvar name)
      (lookup : targetFree name =
        some (mapTypeExpr (color.symbols source) reached.sourceType))
  | boundary
      (view : CostStaticPlanFVarContextInventoryView plan occurrence)
      (stopped : CostStaticPlanStopped source color targetFree view.rawPayload
        plan.abstractPattern)
      (view_eq : view.inventory.view = .stopped stopped)

namespace CostStaticPlanFVarTerminal

/-- Every exact free-variable occurrence has a source-variable or certified
boundary terminal.  Constructor-shaped, binder-shaped, collection-shaped,
and bound-variable reached plans are excluded by the selected-leaf equation.
-/
noncomputable def ofView
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
    CostStaticPlanFVarTerminal plan occurrence := by
  cases view_eq : view.inventory.view with
  | stopped stopped =>
      exact .boundary view stopped view_eq
  | reached reached =>
      have selected := view.selected_eq
      rw [view_eq] at selected
      let origin := CostStaticRegionPlanFVarOrigin.ofAbstractFVar reached.plan
        occurrence.name selected
      cases origin with
      | sourceVariable name name_eq pattern_eq lookup =>
          exact .sourceVariable view reached view_eq name name_eq pattern_eq
            lookup
      | boundary certified certifies content_eq abstract_eq entries_eq =>
          let stopped : CostStaticPlanStopped source color targetFree
              view.rawPayload plan.abstractPattern :=
            { boundarySupport := _
              boundaryType := _
              content := _
              certified := certified
              certifies := certifies
              residual := .hole
              content_eq := by
                simpa [OneHoleContext.fill] using content_eq
              skeletonContext := reached.skeletonContext
              abstract_eq := by
                exact reached.abstract_eq.trans
                  (congrArg reached.skeletonContext.fill abstract_eq) }
          let inventory : CostStaticPlanContextInventoryView source color
              targetFree view.rawPayload plan.abstractPattern
              plan.boundaryTable.entries :=
            { view := .stopped stopped
              entryEmbedding := by
                have embedding := view.inventory.entryEmbedding
                rw [view_eq] at embedding
                simp only [CostStaticPlanContextView.retainedEntries]
                  at embedding
                rw [entries_eq] at embedding
                simpa [CostStaticPlanContextView.retainedEntries, stopped]
                  using embedding }
          let boundaryView : CostStaticPlanFVarContextInventoryView plan
              occurrence :=
            { rawPayload := view.rawPayload
              inventory := inventory
              context_eq := by
                have contextEq := view.context_eq
                rw [view_eq] at contextEq
                simpa [inventory, stopped,
                  CostStaticPlanContextView.abstractContext] using contextEq
              selected_eq := by
                have nameEq :
                    (.fvar (costRegionBoundaryVariableName
                      certified.typed.boundary) : Pattern) =
                      .fvar occurrence.name :=
                  abstract_eq.symm.trans selected
                simpa [inventory, stopped,
                  CostStaticPlanContextView.selectedAbstract] using nameEq }
          exact .boundary boundaryView stopped rfl

/-- Total terminal classification for an exact free-variable occurrence. -/
noncomputable def ofOccurrence
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (occurrence : CostStaticFVarOccurrence plan.abstractPattern) :
    CostStaticPlanFVarTerminal plan occurrence :=
  ofView (Classical.choice (plan.nonempty_fvarContextInventoryView occurrence))

end CostStaticPlanFVarTerminal

end Mettapedia.GSLT.LanguageDef
