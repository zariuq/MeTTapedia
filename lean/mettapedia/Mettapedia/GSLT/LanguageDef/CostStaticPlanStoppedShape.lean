import Mettapedia.GSLT.LanguageDef.CostStaticPlanContextView

/-!
# Shape of the skeleton context retained by a static-region context view

`CostStaticRegionPlan.nonempty_contextInventoryView` returns a context view
whose retained `skeletonContext` is built by exactly two mechanisms: the two
traversal stops install `.hole`, and each returning recursive step installs
one enclosing frame through `CostStaticPlanContextView.liftSkeleton`.  The
frames it can install are drawn from a fixed four-element vocabulary --
constructor application, single binder, multi-binder, collection -- because
those are the only plan constructors with a recursive child.

`CostStaticPlanSkeletonComposed` names that vocabulary.  It is a genuine
restriction on `OneHoleContext`: neither substitution frame is a skeleton
frame, matching the fact that no plan constructor carries a substitution
pattern.

The strengthened totality theorem below reproduces the existing recursion and
additionally returns the shape evidence, so a consumer that classifies stopped
states by their `skeletonContext` -- semantic-cut producers take hypotheses of
the form `state.skeletonContext = .apply quoteConstructor [] ... []` -- can
discharge its side condition by induction on a finite frame grammar instead of
by a case analysis over all one-hole contexts.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open WellSorted

/-- A one-hole context composed exclusively of frames that a static-region
plan traversal can install: the constructor-application frame with its sibling
abstract patterns, the single-binder frame, the multi-binder frame, and the
collection frame with its sibling abstract patterns and residual variable.
There is deliberately no substitution constructor. -/
inductive CostStaticPlanSkeletonComposed : OneHoleContext → Prop where
  | hole : CostStaticPlanSkeletonComposed .hole
  | apply (constructorLabel : String) (before after : List Pattern)
      {inner : OneHoleContext} :
      CostStaticPlanSkeletonComposed inner →
      CostStaticPlanSkeletonComposed
        (.apply constructorLabel before inner after)
  | lambda (binderName : Option String) {inner : OneHoleContext} :
      CostStaticPlanSkeletonComposed inner →
      CostStaticPlanSkeletonComposed (.lambda binderName inner)
  | multiLambda (arity : Nat) (binderNames : List String)
      {inner : OneHoleContext} :
      CostStaticPlanSkeletonComposed inner →
      CostStaticPlanSkeletonComposed (.multiLambda arity binderNames inner)
  | collection (collectionType : CollType) (before after : List Pattern)
      (rest : Option String) {inner : OneHoleContext} :
      CostStaticPlanSkeletonComposed inner →
      CostStaticPlanSkeletonComposed
        (.collection collectionType before inner after rest)

namespace CostStaticPlanSkeletonComposed

/-- Skeleton frames are closed under context composition, which is what
`liftSkeleton` performs on the retained context at every returning step. -/
theorem comp {outerContext innerContext : OneHoleContext}
    (outerComposed : CostStaticPlanSkeletonComposed outerContext)
    (innerComposed : CostStaticPlanSkeletonComposed innerContext) :
    CostStaticPlanSkeletonComposed (outerContext.comp innerContext) := by
  induction outerComposed with
  | hole => simpa [OneHoleContext.comp] using innerComposed
  | apply constructorLabel before after _ inductionHypothesis =>
      simpa [OneHoleContext.comp] using
        CostStaticPlanSkeletonComposed.apply constructorLabel before after
          inductionHypothesis
  | lambda binderName _ inductionHypothesis =>
      simpa [OneHoleContext.comp] using
        CostStaticPlanSkeletonComposed.lambda binderName inductionHypothesis
  | multiLambda arity binderNames _ inductionHypothesis =>
      simpa [OneHoleContext.comp] using
        CostStaticPlanSkeletonComposed.multiLambda arity binderNames
          inductionHypothesis
  | collection collectionType before after rest _ inductionHypothesis =>
      simpa [OneHoleContext.comp] using
        CostStaticPlanSkeletonComposed.collection collectionType before after
          rest inductionHypothesis

/-- Inversion at an application frame. -/
theorem of_apply {constructorLabel : String} {before after : List Pattern}
    {inner : OneHoleContext}
    (composed : CostStaticPlanSkeletonComposed
      (.apply constructorLabel before inner after)) :
    CostStaticPlanSkeletonComposed inner := by
  cases composed
  assumption

/-- Inversion at a single-binder frame. -/
theorem of_lambda {binderName : Option String} {inner : OneHoleContext}
    (composed : CostStaticPlanSkeletonComposed (.lambda binderName inner)) :
    CostStaticPlanSkeletonComposed inner := by
  cases composed
  assumption

/-- Inversion at a multi-binder frame. -/
theorem of_multiLambda {arity : Nat} {binderNames : List String}
    {inner : OneHoleContext}
    (composed : CostStaticPlanSkeletonComposed
      (.multiLambda arity binderNames inner)) :
    CostStaticPlanSkeletonComposed inner := by
  cases composed
  assumption

/-- Inversion at a collection frame. -/
theorem of_collection {collectionType : CollType}
    {before after : List Pattern} {rest : Option String}
    {inner : OneHoleContext}
    (composed : CostStaticPlanSkeletonComposed
      (.collection collectionType before inner after rest)) :
    CostStaticPlanSkeletonComposed inner := by
  cases composed
  assumption

/-- Negative boundary: a substitution body frame is not a skeleton frame. -/
theorem not_substBody (inner : OneHoleContext) (replacement : Pattern) :
    ¬ CostStaticPlanSkeletonComposed (.substBody inner replacement) := by
  intro composed
  cases composed

/-- Negative boundary: a substitution replacement frame is not a skeleton
frame. -/
theorem not_substReplacement (body : Pattern) (inner : OneHoleContext) :
    ¬ CostStaticPlanSkeletonComposed (.substReplacement body inner) := by
  intro composed
  cases composed

end CostStaticPlanSkeletonComposed

/-- Positive example: a nested application-under-binder skeleton. -/
example : CostStaticPlanSkeletonComposed
    (.apply "pair" [.fvar "left"] (.lambda (some "x") .hole) [.fvar "right"]) :=
  .apply "pair" [.fvar "left"] [.fvar "right"] (.lambda (some "x") .hole)

/-- Negative example: the restriction is not vacuous under nesting either --
a substitution frame anywhere on the spine is rejected. -/
example (constructorLabel : String) (before after : List Pattern)
    (inner : OneHoleContext) (replacement : Pattern) :
    ¬ CostStaticPlanSkeletonComposed
      (.apply constructorLabel before (.substBody inner replacement) after) :=
  fun composed =>
    CostStaticPlanSkeletonComposed.not_substBody inner replacement
      (CostStaticPlanSkeletonComposed.of_apply composed)

namespace CostStaticPlanContextView

/-- The retained skeleton context of a one-sided context view, uniformly in
the reached/stopped distinction. -/
def skeletonContext {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern} :
    CostStaticPlanContextView source color targetFree payload rootAbstract →
      OneHoleContext
  | .reached state => state.skeletonContext
  | .stopped state => state.skeletonContext

@[simp]
theorem skeletonContext_reached {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached source color targetFree payload
      rootAbstract) :
    (CostStaticPlanContextView.reached state).skeletonContext =
      state.skeletonContext := rfl

@[simp]
theorem skeletonContext_stopped {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (state : CostStaticPlanStopped source color targetFree payload
      rootAbstract) :
    (CostStaticPlanContextView.stopped state).skeletonContext =
      state.skeletonContext := rfl

/-- Lifting by one frame composes that frame onto the retained context, in
both view cases. -/
@[simp]
theorem skeletonContext_liftSkeleton
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {payload innerAbstract outerAbstract : Pattern}
    (frame : OneHoleContext)
    (frameEq : outerAbstract = frame.fill innerAbstract)
    (view : CostStaticPlanContextView source color targetFree payload
      innerAbstract) :
    (view.liftSkeleton frame frameEq).skeletonContext =
      frame.comp view.skeletonContext := by
  cases view <;> rfl

end CostStaticPlanContextView

/-- An inventory-preserving context view that additionally exposes the frame
grammar of its retained skeleton context. -/
structure CostStaticPlanShapedContextInventoryView (source : CIGSLT)
    (color : CostStaticColor) (targetFree : FreeTypeContext)
    (payload rootAbstract : Pattern)
    (rootEntries : List (TypedCostRegionBoundary source color targetFree))
    extends CostStaticPlanContextInventoryView source color targetFree payload
      rootAbstract rootEntries where
  skeletonComposed : CostStaticPlanSkeletonComposed view.skeletonContext

/-- Shape-preserving total decomposition.  Every successful plan indexed by a
filled context yields an exact sub-plan or intercepted boundary, a proof that
all retained entries belong to the root finite table, and a proof that the
retained skeleton context is composed of plan frames only.

The recursion is the one already used by
`CostStaticRegionPlan.nonempty_contextInventoryView`; the added component is
the frame-grammar witness, which is `.hole` at both traversal stops and one
`CostStaticPlanSkeletonComposed.comp` step at each returning frame. -/
theorem CostStaticRegionPlan.nonempty_shapedContextInventoryView
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
      Nonempty (CostStaticPlanShapedContextInventoryView source color
        targetFree payload plan.abstractPattern plan.boundaryTable.entries)
  | .hole, _, _, _, _, _, pattern, payload, _, plan, fillEq => by
      simp only [OneHoleContext.fill] at fillEq
      subst fillEq
      exact ⟨
        { view := .reached
            { sourceBound := _, targetBound := _, thinning := _
              sourceAvailable := _, outer := _, sourceType := _
              plan := plan, skeletonContext := .hole, abstract_eq := rfl }
          entryEmbedding := CostStaticPlanEntryEmbedding.refl _
          skeletonComposed := .hole }⟩
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
                  certifies := certifies
                  residual := .apply wireLabel before inner after
                  content_eq := fillEq
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _
              skeletonComposed := .hole }⟩
      | application declared rendered current preimage notBare children =>
          obtain ⟨-, argumentsEq⟩ := Pattern.apply.inj fillEq
          obtain ⟨active⟩ :=
            CostStaticArgumentPlan.nonempty_activeAt children argumentsEq
          obtain ⟨inventory⟩ :=
            CostStaticRegionPlan.nonempty_shapedContextInventoryView inner
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
                exact inventory.entryEmbedding.comp active.entryEmbedding
              skeletonComposed := by
                rw [CostStaticPlanContextView.skeletonContext_liftSkeleton]
                exact CostStaticPlanSkeletonComposed.comp
                  (.apply _ _ _ .hole) inventory.skeletonComposed }⟩
  | .lambda binderName inner, _, _, _, _, _, pattern, payload, _, plan,
      fillEq => by
      simp only [OneHoleContext.fill] at fillEq
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          simp at fillEq
      | fvar lookup => simp at fillEq
      | boundaryApplication constructorName rendered outsideCurrent certified
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
            CostStaticRegionPlan.nonempty_shapedContextInventoryView inner
              bodyPlan bodyEq
          let frame : OneHoleContext := .lambda planBinder .hole
          exact ⟨
            { view := inventory.view.liftSkeleton frame (by
                simp [frame, CostStaticRegionPlan.abstractPattern,
                  OneHoleContext.fill])
              entryEmbedding := by
                rw [CostStaticPlanContextView.retainedEntries_liftSkeleton]
                exact inventory.entryEmbedding
              skeletonComposed := by
                rw [CostStaticPlanContextView.skeletonContext_liftSkeleton]
                exact CostStaticPlanSkeletonComposed.comp
                  (.lambda _ .hole) inventory.skeletonComposed }⟩
  | .multiLambda arity binderNames inner, _, _, _, _, _, pattern, payload,
      _, plan, fillEq => by
      simp only [OneHoleContext.fill] at fillEq
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          simp at fillEq
      | fvar lookup => simp at fillEq
      | boundaryApplication constructorName rendered outsideCurrent certified
          certifies => simp at fillEq
      | application declared rendered current preimage notBare children =>
          simp at fillEq
      | lambda bodyPlan => simp at fillEq
      | collection choice selected children => simp at fillEq
      | boundaryCollection currentRejected oppositeChoice oppositeSelected
          certified certifies => simp at fillEq
      | @multiLambda _ _ _ _ _ planArity planBinders _ _ _ bodyPlan =>
          obtain ⟨-, -, bodyEq⟩ := Pattern.multiLambda.inj fillEq
          obtain ⟨inventory⟩ :=
            CostStaticRegionPlan.nonempty_shapedContextInventoryView inner
              bodyPlan bodyEq
          let frame : OneHoleContext :=
            .multiLambda planArity planBinders .hole
          exact ⟨
            { view := inventory.view.liftSkeleton frame (by
                simp [frame, CostStaticRegionPlan.abstractPattern,
                  OneHoleContext.fill])
              entryEmbedding := by
                rw [CostStaticPlanContextView.retainedEntries_liftSkeleton]
                exact inventory.entryEmbedding
              skeletonComposed := by
                rw [CostStaticPlanContextView.skeletonContext_liftSkeleton]
                exact CostStaticPlanSkeletonComposed.comp
                  (.multiLambda _ _ .hole) inventory.skeletonComposed }⟩
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
      | boundaryApplication constructorName rendered outsideCurrent certified
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
                  certifies := certifies
                  residual :=
                    .collection collectionType before inner after rest
                  content_eq := fillEq
                  skeletonContext := .hole
                  abstract_eq := rfl }
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _
              skeletonComposed := .hole }⟩
      | @collection _ _ _ _ _ planCollection _ planRest _ choice selected
          children =>
          obtain ⟨-, elementsEq, -⟩ := Pattern.collection.inj fillEq
          obtain ⟨active⟩ :=
            CostStaticElementPlan.nonempty_activeAt children elementsEq
          obtain ⟨inventory⟩ :=
            CostStaticRegionPlan.nonempty_shapedContextInventoryView inner
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
                exact inventory.entryEmbedding.comp active.entryEmbedding
              skeletonComposed := by
                rw [CostStaticPlanContextView.skeletonContext_liftSkeleton]
                exact CostStaticPlanSkeletonComposed.comp
                  (.collection _ _ _ _ .hole)
                  inventory.skeletonComposed }⟩

/-- Support erasure of the shape-preserving decomposition: the same hypotheses
as `CostStaticRegionPlan.nonempty_contextView`, with the frame grammar of the
retained skeleton context carried along. -/
theorem CostStaticRegionPlan.nonempty_shapedContextView
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
    Nonempty { view : CostStaticPlanContextView source color targetFree payload
        plan.abstractPattern //
      CostStaticPlanSkeletonComposed view.skeletonContext } := by
  obtain ⟨shaped⟩ :=
    plan.nonempty_shapedContextInventoryView context fillEq
  exact ⟨⟨shaped.view, shaped.skeletonComposed⟩⟩

end Mettapedia.GSLT.LanguageDef
