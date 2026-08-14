import Mettapedia.GSLT.LanguageDef.CostStructuralSelection
import Mettapedia.GSLT.LanguageDef.CostStaticPlanContextView

/-!
# Selection inversion for Cost static-plan abstractions

A static plan abstraction retains ordinary structural positions but replaces
each foreign boundary by one rigid variable.  Inverting a selected abstract
position therefore has two honest outcomes: a structural position reaches a
sub-plan, while a boundary variable stops at its certified hidden content.

The result uses the existing inventory context view.  In particular, it
retains the selected sub-plan table or the exact intercepted boundary and its
proof-relevant embedding into the root table.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open WellSorted

namespace CostStaticPlanContextView

/-- The abstract zipper retained by a reached or stopped plan view. -/
def abstractContext {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern} :
    CostStaticPlanContextView source color targetFree payload rootAbstract →
      OneHoleContext
  | .reached state => state.skeletonContext
  | .stopped state => state.skeletonContext

/-- The abstract subterm selected by a reached or stopped plan view. -/
def selectedAbstract {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern} :
    CostStaticPlanContextView source color targetFree payload rootAbstract →
      Pattern
  | .reached state => state.plan.abstractPattern
  | .stopped state =>
      .fvar (costRegionBoundaryVariableName state.certified.typed.boundary)

/-- A context view is an exact factorization of its root abstract pattern. -/
@[simp]
theorem abstractContext_fill_selectedAbstract
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (view : CostStaticPlanContextView source color targetFree payload
      rootAbstract) :
    view.abstractContext.fill view.selectedAbstract = rootAbstract := by
  cases view with
  | reached state => exact state.abstract_eq.symm
  | stopped state => exact state.abstract_eq.symm

@[simp]
theorem abstractContext_liftSkeleton
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {payload innerAbstract outerAbstract : Pattern}
    (frame : OneHoleContext)
    (frameEq : outerAbstract = frame.fill innerAbstract)
    (view : CostStaticPlanContextView source color targetFree payload
      innerAbstract) :
    (view.liftSkeleton frame frameEq).abstractContext =
      frame.comp view.abstractContext := by
  cases view <;> rfl

@[simp]
theorem selectedAbstract_liftSkeleton
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {payload innerAbstract outerAbstract : Pattern}
    (frame : OneHoleContext)
    (frameEq : outerAbstract = frame.fill innerAbstract)
    (view : CostStaticPlanContextView source color targetFree payload
      innerAbstract) :
    (view.liftSkeleton frame frameEq).selectedAbstract =
      view.selectedAbstract := by
  cases view <;> rfl

end CostStaticPlanContextView

/-! ## Abstract child selection in ordered plan spines -/

/-- An abstract argument-list split selects an actual child plan and retains
both its raw argument position and its boundary-table embedding. -/
theorem CostStaticArgumentPlan.nonempty_activeAbstractAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    ∀ {abstractBefore : List Pattern}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {wireName : String} {before arguments : List Pattern}
      {parameters : List TermParam}
      (spine : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters)
      {middle : Pattern} {abstractAfter : List Pattern},
      spine.abstractPatterns =
        abstractBefore ++ middle :: abstractAfter →
      ∃ rawBefore rawMiddle rawAfter,
        ∃ active : CostStaticArgumentPlanActive source color targetFree spine
          rawBefore rawMiddle rawAfter,
        active.beforeAbstracts = abstractBefore ∧
          active.head.abstractPattern = middle ∧
          active.afterAbstracts = abstractAfter
  | [], _, _, _, _, _, _, _, _, _, spine, middle, abstractAfter, split => by
      cases spine with
      | nil => simp [CostStaticArgumentPlan.abstractPatterns] at split
      | cons representation parameterType head tail =>
          simp only [CostStaticArgumentPlan.abstractPatterns,
            List.nil_append, List.cons.injEq] at split
          let active : CostStaticArgumentPlanActive source color targetFree
              (.cons representation parameterType head tail) [] _ _ :=
            { sourceExpected := _
              position := _
              position_eq := (List.append_nil _).symm
              head := head
              beforeAbstracts := []
              afterAbstracts := tail.abstractPatterns
              abstracts_eq := rfl
              entryEmbedding := by
                change CostStaticPlanEntryEmbedding source color targetFree
                  head.boundaryTable.entries
                  (TypedCostRegionBoundaryTable.append head.boundaryTable
                    tail.boundaryTable).entries
                rw [TypedCostRegionBoundaryTable.entries_append]
                exact CostStaticPlanEntryEmbedding.appendLeft _ _ }
          exact ⟨[], _, _, active, rfl, split.1, split.2⟩
  | abstractHead :: abstractBefore, _, _, _, _, _, _, _, _, _, spine,
      middle, abstractAfter, split => by
      cases spine with
      | nil => simp [CostStaticArgumentPlan.abstractPatterns] at split
      | @cons _ _ _ _ _ _ _ rawArgument _ _ _ _ representation
          parameterType head tail =>
          simp only [CostStaticArgumentPlan.abstractPatterns,
            List.cons_append, List.cons.injEq] at split
          obtain ⟨rawBefore, rawMiddle, rawAfter, nested, beforeEquality,
              middleEquality, afterEquality⟩ :=
            CostStaticArgumentPlan.nonempty_activeAbstractAt tail split.2
          let active : CostStaticArgumentPlanActive source color targetFree
              (.cons representation parameterType head tail)
              (rawArgument :: rawBefore) rawMiddle rawAfter :=
            { sourceExpected := nested.sourceExpected
              position := nested.position
              position_eq := nested.position_eq.trans (by simp)
              head := nested.head
              beforeAbstracts := head.abstractPattern ::
                nested.beforeAbstracts
              afterAbstracts := nested.afterAbstracts
              abstracts_eq := by
                simp [CostStaticArgumentPlan.abstractPatterns,
                  nested.abstracts_eq]
              entryEmbedding := by
                change CostStaticPlanEntryEmbedding source color targetFree
                  nested.head.boundaryTable.entries
                  (TypedCostRegionBoundaryTable.append head.boundaryTable
                    tail.boundaryTable).entries
                rw [TypedCostRegionBoundaryTable.entries_append]
                exact nested.entryEmbedding.comp
                  (CostStaticPlanEntryEmbedding.appendRight _ _) }
          exact ⟨rawArgument :: rawBefore, rawMiddle, rawAfter, active,
            by simp [active, split.1, beforeEquality], middleEquality,
            afterEquality⟩

/-- Collection-element counterpart of
`CostStaticArgumentPlan.nonempty_activeAbstractAt`. -/
theorem CostStaticElementPlan.nonempty_activeAbstractAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    ∀ {abstractBefore : List Pattern}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {collectionType : CollType} {before elements : List Pattern}
      {rest : Option String} {sourceElementType : TypeExpr}
      (spine : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType)
      {middle : Pattern} {abstractAfter : List Pattern},
      spine.abstractPatterns =
        abstractBefore ++ middle :: abstractAfter →
      ∃ rawBefore rawMiddle rawAfter,
        ∃ active : CostStaticElementPlanActive source color targetFree spine
          rawBefore rawMiddle rawAfter,
        active.beforeAbstracts = abstractBefore ∧
          active.head.abstractPattern = middle ∧
          active.afterAbstracts = abstractAfter
  | [], _, _, _, _, _, _, _, _, _, _, spine, middle, abstractAfter,
      split => by
      cases spine with
      | nil => simp [CostStaticElementPlan.abstractPatterns] at split
      | cons head tail =>
          simp only [CostStaticElementPlan.abstractPatterns,
            List.nil_append, List.cons.injEq] at split
          let active : CostStaticElementPlanActive source color targetFree
              (.cons head tail) [] _ _ :=
            { position := _
              position_eq := (List.append_nil _).symm
              head := head
              beforeAbstracts := []
              afterAbstracts := tail.abstractPatterns
              abstracts_eq := rfl
              entryEmbedding := by
                change CostStaticPlanEntryEmbedding source color targetFree
                  head.boundaryTable.entries
                  (TypedCostRegionBoundaryTable.append head.boundaryTable
                    tail.boundaryTable).entries
                rw [TypedCostRegionBoundaryTable.entries_append]
                exact CostStaticPlanEntryEmbedding.appendLeft _ _ }
          exact ⟨[], _, _, active, rfl, split.1, split.2⟩
  | abstractHead :: abstractBefore, _, _, _, _, _, _, _, _, _, _, spine,
      middle, abstractAfter, split => by
      cases spine with
      | nil => simp [CostStaticElementPlan.abstractPatterns] at split
      | @cons _ _ _ _ _ _ _ rawElement _ _ _ head tail =>
          simp only [CostStaticElementPlan.abstractPatterns,
            List.cons_append, List.cons.injEq] at split
          obtain ⟨rawBefore, rawMiddle, rawAfter, nested, beforeEquality,
              middleEquality, afterEquality⟩ :=
            CostStaticElementPlan.nonempty_activeAbstractAt tail split.2
          let active : CostStaticElementPlanActive source color targetFree
              (.cons head tail) (rawElement :: rawBefore) rawMiddle rawAfter :=
            { position := nested.position
              position_eq := nested.position_eq.trans (by simp)
              head := nested.head
              beforeAbstracts := head.abstractPattern ::
                nested.beforeAbstracts
              afterAbstracts := nested.afterAbstracts
              abstracts_eq := by
                simp [CostStaticElementPlan.abstractPatterns,
                  nested.abstracts_eq]
              entryEmbedding := by
                change CostStaticPlanEntryEmbedding source color targetFree
                  nested.head.boundaryTable.entries
                  (TypedCostRegionBoundaryTable.append head.boundaryTable
                    tail.boundaryTable).entries
                rw [TypedCostRegionBoundaryTable.entries_append]
                exact nested.entryEmbedding.comp
                  (CostStaticPlanEntryEmbedding.appendRight _ _) }
          exact ⟨rawElement :: rawBefore, rawMiddle, rawAfter, active,
            by simp [active, split.1, beforeEquality], middleEquality,
            afterEquality⟩

/-! ## Total selection inversion -/

/-- Every abstract-plan occurrence identifies either an exact reached
sub-plan or an intercepted certified boundary.  The selected raw payload,
abstract zipper, selected abstract pattern, and finite table position are all
retained in the returned inventory view. -/
theorem CostStaticRegionPlan.exists_contextInventoryView_of_abstractFill
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    ∀ (abstractContext : OneHoleContext)
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      {abstractPayload : Pattern},
      plan.abstractPattern = abstractContext.fill abstractPayload →
      ∃ rawPayload,
        ∃ inventory : CostStaticPlanContextInventoryView source color
          targetFree rawPayload plan.abstractPattern
            plan.boundaryTable.entries,
        inventory.view.abstractContext = abstractContext ∧
          inventory.view.selectedAbstract = abstractPayload
  | .hole, _, _, _, _, _, _, _, plan, abstractPayload, fillEq => by
      cases plan with
      | boundaryApplication constructor rendered outsideCurrent certified
          certifies =>
          exact ⟨_,
            { view := .stopped
                { boundarySupport := _
                  boundaryType := _
                  content := _
                  certified := certified
                  certifies := certifies
                  residual := .hole
                  content_eq := rfl
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _ },
            rfl, fillEq⟩
      | boundaryCollection currentRejected oppositeChoice oppositeSelected
          certified certifies =>
          exact ⟨_,
            { view := .stopped
                { boundarySupport := _
                  boundaryType := _
                  content := _
                  certified := certified
                  certifies := certifies
                  residual := .hole
                  content_eq := rfl
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _ },
            rfl, fillEq⟩
      | bvar sourceIndex lookup correspondence availableScope =>
          exact ⟨_,
            { view := .reached
                { sourceBound := _
                  targetBound := _
                  thinning := _
                  sourceAvailable := _
                  outer := _
                  sourceType := _
                  plan := .bvar sourceIndex lookup correspondence
                    availableScope
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _ },
            rfl, fillEq⟩
      | fvar lookup =>
          exact ⟨_,
            { view := .reached
                { sourceBound := _
                  targetBound := _
                  thinning := _
                  sourceAvailable := _
                  outer := _
                  sourceType := _
                  plan := .fvar lookup
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _ },
            rfl, fillEq⟩
      | application constructor rendered current preimage notBare children =>
          exact ⟨_,
            { view := .reached
                { sourceBound := _
                  targetBound := _
                  thinning := _
                  sourceAvailable := _
                  outer := _
                  sourceType := _
                  plan := .application constructor rendered current preimage
                    notBare children
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _ },
            rfl, fillEq⟩
      | lambda bodyPlan =>
          exact ⟨_,
            { view := .reached
                { sourceBound := _
                  targetBound := _
                  thinning := _
                  sourceAvailable := _
                  outer := _
                  sourceType := _
                  plan := .lambda bodyPlan
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _ },
            rfl, fillEq⟩
      | multiLambda bodyPlan =>
          exact ⟨_,
            { view := .reached
                { sourceBound := _
                  targetBound := _
                  thinning := _
                  sourceAvailable := _
                  outer := _
                  sourceType := _
                  plan := .multiLambda bodyPlan
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _ },
            rfl, fillEq⟩
      | collection choice selected children =>
          exact ⟨_,
            { view := .reached
                { sourceBound := _
                  targetBound := _
                  thinning := _
                  sourceAvailable := _
                  outer := _
                  sourceType := _
                  plan := .collection choice selected children
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _ },
            rfl, fillEq⟩
  | .apply contextLabel before inner after, _, _, _, _, _, _, _, plan,
      abstractPayload, fillEq => by
      cases plan with
      | application constructor rendered current preimage notBare children =>
          simp only [CostStaticRegionPlan.abstractPattern] at fillEq
          obtain ⟨labelEquality, argumentsEquality⟩ :=
            Pattern.apply.inj fillEq
          obtain ⟨rawBefore, rawMiddle, rawAfter, active, beforeEquality,
              middleEquality, afterEquality⟩ :=
            children.nonempty_activeAbstractAt argumentsEquality
          obtain ⟨rawPayload, nested, nestedContext, nestedPayload⟩ :=
            exists_contextInventoryView_of_abstractFill inner active.head
              middleEquality
          let frame : OneHoleContext :=
            .apply preimage.sourceConstructor.1.label before .hole after
          have frameEq :
              (CostStaticRegionPlan.application constructor rendered current
                preimage notBare children).abstractPattern =
                frame.fill active.head.abstractPattern := by
            simp [frame, CostStaticRegionPlan.abstractPattern,
              OneHoleContext.fill, active.abstracts_eq, beforeEquality,
              afterEquality]
          exact ⟨rawPayload,
            { view := nested.view.liftSkeleton frame frameEq
              entryEmbedding := by
                rw [CostStaticPlanContextView.retainedEntries_liftSkeleton]
                exact nested.entryEmbedding.comp active.entryEmbedding },
            by
              simp [frame, nestedContext, OneHoleContext.comp, labelEquality],
            by simpa using nestedPayload⟩
      | bvar | fvar | boundaryApplication | lambda | multiLambda |
          collection | boundaryCollection =>
          cases fillEq
  | .lambda contextBinder inner, _, _, _, _, _, _, _, plan, abstractPayload,
      fillEq => by
      cases plan with
      | @lambda _ _ _ _ _ planBinder _ _ _ bodyPlan =>
          simp only [CostStaticRegionPlan.abstractPattern] at fillEq
          obtain ⟨binderEquality, bodyEquality⟩ := Pattern.lambda.inj fillEq
          obtain ⟨rawPayload, nested, nestedContext, nestedPayload⟩ :=
            exists_contextInventoryView_of_abstractFill inner bodyPlan
              bodyEquality
          let frame : OneHoleContext := .lambda planBinder .hole
          have frameEq :
              (CostStaticRegionPlan.lambda bodyPlan).abstractPattern =
                frame.fill bodyPlan.abstractPattern := by
            rfl
          exact ⟨rawPayload,
            { view := nested.view.liftSkeleton frame frameEq
              entryEmbedding := by
                rw [CostStaticPlanContextView.retainedEntries_liftSkeleton]
                exact nested.entryEmbedding },
            by simp [frame, nestedContext, OneHoleContext.comp, binderEquality],
            by simpa using nestedPayload⟩
      | bvar | fvar | boundaryApplication | application | multiLambda |
          collection | boundaryCollection =>
          cases fillEq
  | .multiLambda contextArity contextBinders inner, _, _, _, _, _, _, _, plan,
      abstractPayload, fillEq => by
      cases plan with
      | @multiLambda _ _ _ _ _ planArity planBinders _ _ _ bodyPlan =>
          simp only [CostStaticRegionPlan.abstractPattern] at fillEq
          obtain ⟨arityEquality, bindersEquality, bodyEquality⟩ :=
            Pattern.multiLambda.inj fillEq
          obtain ⟨rawPayload, nested, nestedContext, nestedPayload⟩ :=
            exists_contextInventoryView_of_abstractFill inner bodyPlan
              bodyEquality
          let frame : OneHoleContext :=
            .multiLambda planArity planBinders .hole
          have frameEq :
              (CostStaticRegionPlan.multiLambda bodyPlan).abstractPattern =
                frame.fill bodyPlan.abstractPattern := by
            rfl
          exact ⟨rawPayload,
            { view := nested.view.liftSkeleton frame frameEq
              entryEmbedding := by
                rw [CostStaticPlanContextView.retainedEntries_liftSkeleton]
                exact nested.entryEmbedding },
            by
              simp [frame, nestedContext, OneHoleContext.comp, arityEquality,
                bindersEquality],
            by simpa using nestedPayload⟩
      | bvar | fvar | boundaryApplication | application | lambda |
          collection | boundaryCollection =>
          cases fillEq
  | .substBody inner replacement, _, _, _, _, _, _, _, plan, abstractPayload,
      fillEq => by
      cases plan <;> cases fillEq
  | .substReplacement body inner, _, _, _, _, _, _, _, plan, abstractPayload,
      fillEq => by
      cases plan <;> cases fillEq
  | .collection contextCollection before inner after contextRest, _, _, _, _,
      _, _, _, plan, abstractPayload, fillEq => by
      cases plan with
      | @collection _ _ _ _ _ planCollection _ planRest _ choice selected
          children =>
          simp only [CostStaticRegionPlan.abstractPattern] at fillEq
          obtain ⟨collectionEquality, elementsEquality, restEquality⟩ :=
            Pattern.collection.inj fillEq
          obtain ⟨rawBefore, rawMiddle, rawAfter, active, beforeEquality,
              middleEquality, afterEquality⟩ :=
            children.nonempty_activeAbstractAt elementsEquality
          obtain ⟨rawPayload, nested, nestedContext, nestedPayload⟩ :=
            exists_contextInventoryView_of_abstractFill inner active.head
              middleEquality
          let frame : OneHoleContext :=
            .collection planCollection before .hole after
              (planRest.map costRegionSourceVariableName)
          have frameEq :
              (CostStaticRegionPlan.collection choice selected children
                ).abstractPattern = frame.fill active.head.abstractPattern := by
            simp [frame, CostStaticRegionPlan.abstractPattern,
              OneHoleContext.fill, active.abstracts_eq, beforeEquality,
              afterEquality]
          exact ⟨rawPayload,
            { view := nested.view.liftSkeleton frame frameEq
              entryEmbedding := by
                rw [CostStaticPlanContextView.retainedEntries_liftSkeleton]
                exact nested.entryEmbedding.comp active.entryEmbedding },
            by
              simp [frame, nestedContext, OneHoleContext.comp,
                collectionEquality, restEquality],
            by simpa using nestedPayload⟩
      | bvar | fvar | boundaryApplication | application | lambda |
          multiLambda | boundaryCollection =>
          cases fillEq
termination_by abstractContext => sizeOf abstractContext

/-- Selection-form wrapper around
`exists_contextInventoryView_of_abstractFill`. -/
theorem CostStaticRegionPlan.exists_contextInventoryView_of_abstractSelection
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    {abstractPayload : Pattern} {abstractContext : OneHoleContext}
    (selected : Selects abstractPayload abstractContext plan.abstractPattern) :
    ∃ rawPayload,
      ∃ inventory : CostStaticPlanContextInventoryView source color targetFree
        rawPayload plan.abstractPattern plan.boundaryTable.entries,
      inventory.view.abstractContext = abstractContext ∧
        inventory.view.selectedAbstract = abstractPayload := by
  exact plan.exists_contextInventoryView_of_abstractFill abstractContext
    selected.fill_eq.symm

end Mettapedia.GSLT.LanguageDef
