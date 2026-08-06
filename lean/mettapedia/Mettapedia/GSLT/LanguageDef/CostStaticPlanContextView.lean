import Mettapedia.GSLT.LanguageDef.CostRegionTree

/-!
# One-sided context views of static-region plans

An authored occurrence context selects one path through a successful
static-region plan.  Traversing the plan along that path ends in exactly one
of two states: the traversal reaches an exact sub-plan for the payload, or a
certified foreign boundary encloses the remaining context before the hole.
Both states retain a skeleton-level factorization of the root plan's
abstract pattern, so later semantic closures never re-derive where the
occurrence sits inside the region skeleton.

Substitution contexts need no view constructor: no plan constructor carries
a substitution pattern, so a substitution frame in the context contradicts
the plan's own pattern index.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open WellSorted

/-- The traversal reached an exact sub-plan for the payload.  The complete
planner state at the stop is retained, together with the skeleton context
factoring the root abstract pattern through the sub-plan's abstract
pattern. -/
structure CostStaticPlanReached (source : CIGSLT) (color : CostStaticColor)
    (targetFree : FreeTypeContext) (payload : Pattern)
    (rootAbstract : Pattern) : Type where
  sourceBound : List TypeExpr
  targetBound : List TypeExpr
  thinning : CostStaticBinderThinning source color sourceBound targetBound
  sourceAvailable : List TypeExpr
  outer : OneHoleContext
  sourceType : TypeExpr
  plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
    thinning sourceAvailable outer payload sourceType
  skeletonContext : OneHoleContext
  abstract_eq : rootAbstract = skeletonContext.fill plan.abstractPattern

/-- The traversal stopped at a certified foreign boundary that encloses the
remaining context.  The residual context refills the boundary content from
the payload, and the skeleton context factors the root abstract pattern
through the boundary's rigid variable. -/
structure CostStaticPlanStopped (source : CIGSLT) (color : CostStaticColor)
    (targetFree : FreeTypeContext) (payload : Pattern)
    (rootAbstract : Pattern) : Type where
  boundarySupport : List TypeExpr
  boundaryType : TypeExpr
  content : Pattern
  certified : CertifiedCostRegionBoundary source color targetFree
    boundarySupport boundaryType content
  residual : OneHoleContext
  content_eq : content = residual.fill payload
  skeletonContext : OneHoleContext
  abstract_eq : rootAbstract = skeletonContext.fill
    (.fvar (costRegionBoundaryVariableName certified.typed.boundary))

/-- One-sided context view of a static-region plan along one occurrence
context. -/
inductive CostStaticPlanContextView (source : CIGSLT)
    (color : CostStaticColor) (targetFree : FreeTypeContext)
    (payload : Pattern) (rootAbstract : Pattern) : Type where
  | reached (state : CostStaticPlanReached source color targetFree payload
      rootAbstract)
  | stopped (state : CostStaticPlanStopped source color targetFree payload
      rootAbstract)

namespace CostStaticPlanContextView

/-- The skeleton denotation of a view: the retained skeleton context filled
with the reached sub-plan's abstract pattern or the stopped boundary's
rigid variable. -/
def denotedSkeleton {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern} :
    CostStaticPlanContextView source color targetFree payload rootAbstract →
      Pattern
  | .reached state => state.skeletonContext.fill state.plan.abstractPattern
  | .stopped state => state.skeletonContext.fill
      (.fvar (costRegionBoundaryVariableName state.certified.typed.boundary))

/-- The exact finite boundary entries retained at the traversal stop.  A
reached view retains the whole sub-plan table; a stopped view retains the one
certified boundary that intercepted the occurrence path. -/
def retainedEntries {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern} :
    CostStaticPlanContextView source color targetFree payload rootAbstract →
      List (TypedCostRegionBoundary source color targetFree)
  | .reached state => state.plan.boundaryTable.entries
  | .stopped state => [state.certified.typed]

/-- Erasure: every returned view denotes exactly the root plan's abstract
pattern, so the view is a decomposition of the original plan, not a
reconstruction beside it. -/
theorem denotedSkeleton_eq {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (view : CostStaticPlanContextView source color targetFree payload
      rootAbstract) :
    view.denotedSkeleton = rootAbstract := by
  cases view with
  | reached state => exact state.abstract_eq.symm
  | stopped state => exact state.abstract_eq.symm

/-- Extend the retained skeleton context by one enclosing frame. -/
def liftSkeleton {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload innerAbstract outerAbstract :
      Pattern}
    (frame : OneHoleContext)
    (frameEq : outerAbstract = frame.fill innerAbstract)
    (view : CostStaticPlanContextView source color targetFree payload
      innerAbstract) :
    CostStaticPlanContextView source color targetFree payload
      outerAbstract :=
  match view with
  | .reached state =>
      .reached { state with
        skeletonContext := frame.comp state.skeletonContext
        abstract_eq := by
          rw [OneHoleContext.fill_comp, ← state.abstract_eq]
          exact frameEq }
  | .stopped state =>
      .stopped { state with
        skeletonContext := frame.comp state.skeletonContext
        abstract_eq := by
          rw [OneHoleContext.fill_comp, ← state.abstract_eq]
          exact frameEq }

@[simp]
theorem retainedEntries_liftSkeleton
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload innerAbstract outerAbstract :
      Pattern}
    (frame : OneHoleContext)
    (frameEq : outerAbstract = frame.fill innerAbstract)
    (view : CostStaticPlanContextView source color targetFree payload
      innerAbstract) :
    (view.liftSkeleton frame frameEq).retainedEntries =
      view.retainedEntries := by
  cases view <;> rfl

end CostStaticPlanContextView

/-- A proof-relevant, order-preserving embedding of one finite boundary-entry
inventory into another.  Unlike `List.Sublist`, the retained constructor path
is data: repeated equal boundaries still have distinct replayable positions.
This is an endpoint-local embedding; nonlinear transport between endpoints is
still represented separately by `CostBoundaryFiberMap`. -/
inductive CostStaticPlanEntryEmbedding (source : CIGSLT)
    (color : CostStaticColor) (targetFree : FreeTypeContext) :
    List (TypedCostRegionBoundary source color targetFree) →
      List (TypedCostRegionBoundary source color targetFree) → Type where
  | nil (large : List (TypedCostRegionBoundary source color targetFree)) :
      CostStaticPlanEntryEmbedding source color targetFree [] large
  | keep {entry : TypedCostRegionBoundary source color targetFree}
      {small large : List (TypedCostRegionBoundary source color targetFree)}
      (tail : CostStaticPlanEntryEmbedding source color targetFree small large) :
      CostStaticPlanEntryEmbedding source color targetFree
        (entry :: small) (entry :: large)
  | skip (entry : TypedCostRegionBoundary source color targetFree)
      {small large : List (TypedCostRegionBoundary source color targetFree)}
      (tail : CostStaticPlanEntryEmbedding source color targetFree small large) :
      CostStaticPlanEntryEmbedding source color targetFree small
        (entry :: large)

namespace CostStaticPlanEntryEmbedding

/-- Identity embedding, retaining every finite position. -/
def refl {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    (entries : List (TypedCostRegionBoundary source color targetFree)) →
      CostStaticPlanEntryEmbedding source color targetFree entries entries
  | [] => .nil []
  | _entry :: tail => .keep (refl tail)

/-- Embed the left segment into an appended inventory. -/
def appendLeft {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    (left right : List (TypedCostRegionBoundary source color targetFree)) →
      CostStaticPlanEntryEmbedding source color targetFree left (left ++ right)
  | [], right => .nil right
  | _entry :: tail, right => .keep (appendLeft tail right)

/-- Embed the right segment into an appended inventory. -/
def appendRight {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    (left right : List (TypedCostRegionBoundary source color targetFree)) →
      CostStaticPlanEntryEmbedding source color targetFree right (left ++ right)
  | [], right => refl right
  | entry :: tail, right => .skip entry (appendRight tail right)

/-- Compose retained finite positions without erasing their witness path. -/
def comp {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {first second third :
      List (TypedCostRegionBoundary source color targetFree)} :
    CostStaticPlanEntryEmbedding source color targetFree first second →
      CostStaticPlanEntryEmbedding source color targetFree second third →
        CostStaticPlanEntryEmbedding source color targetFree first third
  | .nil _, _ => .nil _
  | .keep firstTail, .keep secondTail => .keep (comp firstTail secondTail)
  | .skip _ firstTail, .keep secondTail =>
      .skip _ (comp firstTail secondTail)
  | firstMap, .skip entry secondTail =>
      .skip entry (comp firstMap secondTail)

/-- Negative boundary canary: a replayable embedding cannot manufacture a
retained entry when the root inventory is empty. -/
theorem noCreationIntoEmpty {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (entry : TypedCostRegionBoundary source color targetFree)
    (tail : List (TypedCostRegionBoundary source color targetFree)) :
    IsEmpty (CostStaticPlanEntryEmbedding source color targetFree
      (entry :: tail) []) := by
  constructor
  intro embedding
  cases embedding

/-- Forgetting replayable positions yields ordinary membership inclusion. -/
theorem subset {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {small large : List (TypedCostRegionBoundary source color targetFree)}
    (embedding : CostStaticPlanEntryEmbedding source color targetFree small
      large) : small ⊆ large := by
  induction embedding with
  | nil => simp
  | keep tail inductionHypothesis =>
      intro boundary membership
      simp only [List.mem_cons] at membership ⊢
      exact membership.elim Or.inl (fun member => Or.inr
        (inductionHypothesis member))
  | skip entry tail inductionHypothesis =>
      intro boundary membership
      exact List.mem_cons_of_mem _ (inductionHypothesis membership)

end CostStaticPlanEntryEmbedding

/-- A context view together with its exact finite provenance inside the root
plan table.  This is deliberately an inclusion, not a positional zipper:
later generator transport may duplicate or discard entries through a
`CostBoundaryFiberMap`. -/
structure CostStaticPlanContextInventoryView (source : CIGSLT)
    (color : CostStaticColor) (targetFree : FreeTypeContext)
    (payload rootAbstract : Pattern)
    (rootEntries : List (TypedCostRegionBoundary source color targetFree)) :
    Type where
  view : CostStaticPlanContextView source color targetFree payload rootAbstract
  entryEmbedding : CostStaticPlanEntryEmbedding source color targetFree
    view.retainedEntries rootEntries

/-- The active argument selected by a context split of one constructor
spine: the head plan at the exact accumulated position, together with the
abstract factorization of the spine. -/
structure CostStaticArgumentPlanActive (source : CIGSLT)
    (color : CostStaticColor) (targetFree : FreeTypeContext)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {wireName : String} {before arguments : List Pattern}
    {parameters : List TermParam}
    (spine : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName before arguments
      parameters)
    (contextBefore : List Pattern) (middle : Pattern)
    (contextAfter : List Pattern) : Type where
  sourceExpected : TypeExpr
  position : List Pattern
  position_eq : position = before ++ contextBefore
  head : CostStaticRegionPlan source color targetFree sourceBound targetBound
    thinning sourceAvailable
    (outer.comp (.apply wireName position .hole contextAfter))
    middle sourceExpected
  beforeAbstracts : List Pattern
  afterAbstracts : List Pattern
  abstracts_eq : spine.abstractPatterns =
    beforeAbstracts ++ head.abstractPattern :: afterAbstracts
  entryEmbedding : CostStaticPlanEntryEmbedding source color targetFree
    head.boundaryTable.entries spine.boundaryTable.entries

/-- The active element selected by a context split of one collection
spine. -/
structure CostStaticElementPlanActive (source : CIGSLT)
    (color : CostStaticColor) (targetFree : FreeTypeContext)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {before elements : List Pattern}
    {rest : Option String} {sourceElementType : TypeExpr}
    (spine : CostStaticElementPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer collectionType before
      elements rest sourceElementType)
    (contextBefore : List Pattern) (middle : Pattern)
    (contextAfter : List Pattern) : Type where
  position : List Pattern
  position_eq : position = before ++ contextBefore
  head : CostStaticRegionPlan source color targetFree sourceBound targetBound
    thinning sourceAvailable
    (outer.comp (.collection collectionType position .hole contextAfter
      rest))
    middle sourceElementType
  beforeAbstracts : List Pattern
  afterAbstracts : List Pattern
  abstracts_eq : spine.abstractPatterns =
    beforeAbstracts ++ head.abstractPattern :: afterAbstracts
  entryEmbedding : CostStaticPlanEntryEmbedding source color targetFree
    head.boundaryTable.entries spine.boundaryTable.entries

/-- Every context split of a constructor spine selects one active argument
plan at the exact accumulated position. -/
theorem CostStaticArgumentPlan.nonempty_activeAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    ∀ {contextBefore : List Pattern}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {wireName : String} {before arguments : List Pattern}
      {parameters : List TermParam}
      (spine : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters)
      {middle : Pattern} {contextAfter : List Pattern},
      arguments = contextBefore ++ middle :: contextAfter →
      Nonempty (CostStaticArgumentPlanActive source color targetFree spine
        contextBefore middle contextAfter)
  | [], _, _, _, _, _, _, _, _, _, spine, middle, contextAfter, split => by
      cases spine with
      | nil => simp at split
      | cons representation parameterType head tail =>
          obtain ⟨headEq, tailEq⟩ := List.cons.inj split
          subst headEq
          subst tailEq
          exact ⟨{ sourceExpected := _
                   position := _
                   position_eq := (List.append_nil _).symm
                   head := head
                   beforeAbstracts := []
                   afterAbstracts := tail.abstractPatterns
                   abstracts_eq := rfl
                   entryEmbedding := by
                     change CostStaticPlanEntryEmbedding source color
                       targetFree head.boundaryTable.entries
                       (TypedCostRegionBoundaryTable.append head.boundaryTable
                         tail.boundaryTable).entries
                     rw [TypedCostRegionBoundaryTable.entries_append]
                     exact CostStaticPlanEntryEmbedding.appendLeft _ _ }⟩
  | sibling :: contextRest, _, _, _, _, _, _, _, _, _, spine, middle,
      contextAfter, split => by
      cases spine with
      | nil => simp at split
      | cons representation parameterType head tail =>
          obtain ⟨headEq, tailEq⟩ := List.cons.inj split
          subst headEq
          obtain ⟨active⟩ :=
            CostStaticArgumentPlan.nonempty_activeAt tail tailEq
          refine ⟨{ sourceExpected := active.sourceExpected
                    position := active.position
                    position_eq := active.position_eq.trans
                      (by simp)
                    head := active.head
                    beforeAbstracts :=
                      head.abstractPattern :: active.beforeAbstracts
                    afterAbstracts := active.afterAbstracts
                    abstracts_eq := ?_
                    entryEmbedding := ?_ }⟩
          simp [CostStaticArgumentPlan.abstractPatterns,
            active.abstracts_eq]
          change CostStaticPlanEntryEmbedding source color targetFree
            active.head.boundaryTable.entries
            (TypedCostRegionBoundaryTable.append head.boundaryTable
              tail.boundaryTable).entries
          rw [TypedCostRegionBoundaryTable.entries_append]
          exact active.entryEmbedding.comp
            (CostStaticPlanEntryEmbedding.appendRight _ _)

/-- Every context split of a collection spine selects one active element
plan at the exact accumulated position. -/
theorem CostStaticElementPlan.nonempty_activeAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    ∀ {contextBefore : List Pattern}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {collectionType : CollType} {before elements : List Pattern}
      {rest : Option String} {sourceElementType : TypeExpr}
      (spine : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType)
      {middle : Pattern} {contextAfter : List Pattern},
      elements = contextBefore ++ middle :: contextAfter →
      Nonempty (CostStaticElementPlanActive source color targetFree spine
        contextBefore middle contextAfter)
  | [], _, _, _, _, _, _, _, _, _, _, spine, middle, contextAfter, split => by
      cases spine with
      | nil => simp at split
      | cons head tail =>
          obtain ⟨headEq, tailEq⟩ := List.cons.inj split
          subst headEq
          subst tailEq
          exact ⟨{ position := _
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
                     exact CostStaticPlanEntryEmbedding.appendLeft _ _ }⟩
  | sibling :: contextRest, _, _, _, _, _, _, _, _, _, _, spine, middle,
      contextAfter, split => by
      cases spine with
      | nil => simp at split
      | cons head tail =>
          obtain ⟨headEq, tailEq⟩ := List.cons.inj split
          subst headEq
          obtain ⟨active⟩ :=
            CostStaticElementPlan.nonempty_activeAt tail tailEq
          refine ⟨{ position := active.position
                    position_eq := active.position_eq.trans
                      (by simp)
                    head := active.head
                    beforeAbstracts :=
                      head.abstractPattern :: active.beforeAbstracts
                    afterAbstracts := active.afterAbstracts
                    abstracts_eq := ?_
                    entryEmbedding := ?_ }⟩
          simp [CostStaticElementPlan.abstractPatterns,
            active.abstracts_eq]
          change CostStaticPlanEntryEmbedding source color targetFree
            active.head.boundaryTable.entries
            (TypedCostRegionBoundaryTable.append head.boundaryTable
              tail.boundaryTable).entries
          rw [TypedCostRegionBoundaryTable.entries_append]
          exact active.entryEmbedding.comp
            (CostStaticPlanEntryEmbedding.appendRight _ _)

/-- Inventory-preserving total decomposition.  Every successful plan indexed
by a filled context yields an exact sub-plan or intercepted boundary together
with a proof that all retained entries belong to the root finite table. -/
theorem CostStaticRegionPlan.nonempty_contextInventoryView
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} :
    ∀ (context : OneHoleContext)
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern payload : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType),
      pattern = context.fill payload →
      Nonempty (CostStaticPlanContextInventoryView source color targetFree
        payload plan.abstractPattern plan.boundaryTable.entries)
  | .hole, _, _, _, _, _, pattern, payload, _, plan, fillEq => by
      simp only [OneHoleContext.fill] at fillEq
      subst fillEq
      exact ⟨
        { view := .reached
            { sourceBound := _, targetBound := _, thinning := _
              sourceAvailable := _, outer := _, sourceType := _
              plan := plan, skeletonContext := .hole, abstract_eq := rfl }
          entryEmbedding := CostStaticPlanEntryEmbedding.refl _ }⟩
  | .apply wireLabel before inner after, _, _, _, _, _, pattern, payload,
      _, plan, fillEq => by
      simp only [OneHoleContext.fill] at fillEq
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          simp at fillEq
      | fvar lookup => simp at fillEq
      | lambda bodyPlan => simp at fillEq
      | multiLambda bodyPlan => simp at fillEq
      | collection choice selected children => simp at fillEq
      | boundaryCollection currentRejected oppositeChoice oppositeSelected
          certified certifies => simp at fillEq
      | boundaryApplication declaredConstructor rendered outsideCurrent
          certified certifies =>
          exact ⟨
            { view := .stopped
                { boundarySupport := _, boundaryType := _, content := _
                  certified := certified
                  residual := .apply wireLabel before inner after
                  content_eq := fillEq
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _ }⟩
      | application declared rendered current preimage notBare children =>
          obtain ⟨-, argumentsEq⟩ := Pattern.apply.inj fillEq
          obtain ⟨active⟩ :=
            CostStaticArgumentPlan.nonempty_activeAt children argumentsEq
          obtain ⟨inventory⟩ :=
            CostStaticRegionPlan.nonempty_contextInventoryView inner
              active.head rfl
          let frame : OneHoleContext :=
            .apply preimage.sourceConstructor.1.label
            active.beforeAbstracts .hole active.afterAbstracts
          exact ⟨
            { view := inventory.view.liftSkeleton frame (by
                simp [frame, CostStaticRegionPlan.abstractPattern,
                  OneHoleContext.fill, active.abstracts_eq])
              entryEmbedding := by
                rw [CostStaticPlanContextView.retainedEntries_liftSkeleton]
                exact inventory.entryEmbedding.comp active.entryEmbedding }⟩
  | .lambda binderName inner, _, _, _, _, _, pattern, payload, _, plan,
      fillEq => by
      simp only [OneHoleContext.fill] at fillEq
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          simp at fillEq
      | fvar lookup => simp at fillEq
      | boundaryApplication constructor rendered outsideCurrent certified
          certifies => simp at fillEq
      | application declared rendered current preimage notBare children =>
          simp at fillEq
      | multiLambda bodyPlan => simp at fillEq
      | collection choice selected children => simp at fillEq
      | boundaryCollection currentRejected oppositeChoice oppositeSelected
          certified certifies => simp at fillEq
      | @lambda _ _ _ _ _ planBinder _ _ _ bodyPlan =>
          obtain ⟨-, bodyEq⟩ := Pattern.lambda.inj fillEq
          obtain ⟨inventory⟩ :=
            CostStaticRegionPlan.nonempty_contextInventoryView inner bodyPlan
              bodyEq
          let frame : OneHoleContext := .lambda planBinder .hole
          exact ⟨
            { view := inventory.view.liftSkeleton frame (by
                simp [frame, CostStaticRegionPlan.abstractPattern,
                  OneHoleContext.fill])
              entryEmbedding := by
                rw [CostStaticPlanContextView.retainedEntries_liftSkeleton]
                exact inventory.entryEmbedding }⟩
  | .multiLambda arity binderNames inner, _, _, _, _, _, pattern, payload,
      _, plan, fillEq => by
      simp only [OneHoleContext.fill] at fillEq
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          simp at fillEq
      | fvar lookup => simp at fillEq
      | boundaryApplication constructor rendered outsideCurrent certified
          certifies => simp at fillEq
      | application declared rendered current preimage notBare children =>
          simp at fillEq
      | lambda bodyPlan => simp at fillEq
      | collection choice selected children => simp at fillEq
      | boundaryCollection currentRejected oppositeChoice oppositeSelected
          certified certifies => simp at fillEq
      | @multiLambda _ _ _ _ _ planArity planBinders _ _ _ bodyPlan =>
          obtain ⟨-, -, bodyEq⟩ :=
            Pattern.multiLambda.inj fillEq
          obtain ⟨inventory⟩ :=
            CostStaticRegionPlan.nonempty_contextInventoryView inner bodyPlan
              bodyEq
          let frame : OneHoleContext :=
            .multiLambda planArity planBinders .hole
          exact ⟨
            { view := inventory.view.liftSkeleton frame (by
                simp [frame, CostStaticRegionPlan.abstractPattern,
                  OneHoleContext.fill])
              entryEmbedding := by
                rw [CostStaticPlanContextView.retainedEntries_liftSkeleton]
                exact inventory.entryEmbedding }⟩
  | .substBody inner replacement, _, _, _, _, _, pattern, payload, _, plan,
      fillEq => by
      simp only [OneHoleContext.fill] at fillEq
      cases plan <;> simp at fillEq
  | .substReplacement body inner, _, _, _, _, _, pattern, payload, _, plan,
      fillEq => by
      simp only [OneHoleContext.fill] at fillEq
      cases plan <;> simp at fillEq
  | .collection collectionType before inner after rest, _, _, _, _, _,
      pattern, payload, _, plan, fillEq => by
      simp only [OneHoleContext.fill] at fillEq
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          simp at fillEq
      | fvar lookup => simp at fillEq
      | boundaryApplication constructor rendered outsideCurrent certified
          certifies => simp at fillEq
      | application declared rendered current preimage notBare children =>
          simp at fillEq
      | lambda bodyPlan => simp at fillEq
      | multiLambda bodyPlan => simp at fillEq
      | boundaryCollection currentRejected oppositeChoice oppositeSelected
          certified certifies =>
          exact ⟨
            { view := .stopped
                { boundarySupport := _, boundaryType := _, content := _
                  certified := certified
                  residual :=
                    .collection collectionType before inner after rest
                  content_eq := fillEq
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _ }⟩
      | @collection _ _ _ _ _ planCollection _ planRest _ choice selected
          children =>
          obtain ⟨-, elementsEq, -⟩ := Pattern.collection.inj fillEq
          obtain ⟨active⟩ :=
            CostStaticElementPlan.nonempty_activeAt children elementsEq
          obtain ⟨inventory⟩ :=
            CostStaticRegionPlan.nonempty_contextInventoryView inner
              active.head rfl
          let frame : OneHoleContext :=
            .collection planCollection active.beforeAbstracts .hole
              active.afterAbstracts
              (planRest.map costRegionSourceVariableName)
          exact ⟨
            { view := inventory.view.liftSkeleton frame (by
                simp [frame, CostStaticRegionPlan.abstractPattern,
                  OneHoleContext.fill, active.abstracts_eq])
              entryEmbedding := by
                rw [CostStaticPlanContextView.retainedEntries_liftSkeleton]
                exact inventory.entryEmbedding.comp active.entryEmbedding }⟩

/-- Support erasure of the inventory-preserving decomposition recovers the
original one-sided context view theorem. -/
theorem CostStaticRegionPlan.nonempty_contextView
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (context : OneHoleContext)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (fillEq : pattern = context.fill payload) :
    Nonempty (CostStaticPlanContextView source color targetFree payload
      plan.abstractPattern) := by
  obtain ⟨inventory⟩ := plan.nonempty_contextInventoryView context fillEq
  exact ⟨inventory.view⟩

end Mettapedia.GSLT.LanguageDef
