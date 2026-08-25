import Mettapedia.GSLT.LanguageDef.CostStaticPlanStopCarriers

/-!
# The lockstep canonical-alignment transport

The mutual region/argument/element descent that carries generated-pattern
canonical structure onto the source-plan abstractions, together with its
private index machinery and the strictly-decreasing homogeneous child
descent.  This is the heaviest compilation unit of the lane; it is kept in
its own module so that edits to the parallel and producer layers do not
re-elaborate it.
-/
namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open WellSorted
mutual
  /-- Change the leaf relation of a canonical structural alignment. -/
  theorem canonicalStopAligned_map
      {declaration : ReflectivePresentationDecl}
      {first second : Pattern → Pattern → Prop}
      (transfer : ∀ {left right}, first left right → second left right) :
      ∀ {left right}, CanonicalStopAligned declaration first left right →
        CanonicalStopAligned declaration second left right
    | _, _, .leaf given => .leaf (transfer given)
    | _, _, .bvar index => .bvar index
    | _, _, .fvar name => .fvar name
    | _, _, .apply ne arguments =>
        .apply ne (canonicalStopAlignedList_map transfer arguments)
    | _, _, .lambda binder body =>
        .lambda binder (canonicalStopAligned_map transfer body)
    | _, _, .multiLambda arity binders body =>
        .multiLambda arity binders (canonicalStopAligned_map transfer body)
    | _, _, .subst body replacement =>
        .subst (canonicalStopAligned_map transfer body)
          (canonicalStopAligned_map transfer replacement)
    | _, _, .collection ne elements =>
        .collection ne (canonicalStopAlignedList_map transfer elements)
    | _, _, .collectionRest collectionType rest elements =>
        .collectionRest collectionType rest
          (canonicalStopAlignedList_map transfer elements)

  /-- List companion of `canonicalStopAligned_map`. -/
  theorem canonicalStopAlignedList_map
      {declaration : ReflectivePresentationDecl}
      {first second : Pattern → Pattern → Prop}
      (transfer : ∀ {left right}, first left right → second left right) :
      ∀ {left right}, CanonicalStopAlignedList declaration first left right →
        CanonicalStopAlignedList declaration second left right
    | _, _, .nil => .nil
    | _, _, .cons head tail =>
        .cons (canonicalStopAligned_map transfer head)
          (canonicalStopAlignedList_map transfer tail)
end

/-- Prefix one proof-relevant type route by an earlier descent. -/
def CostCanonicalTypeRoute.prepend
    {source : CIGSLT} {color : CostStaticColor}
    {root middle endpoint : TypeExpr}
    (priorRoute : CostCanonicalTypeRoute source color root middle) :
    CostCanonicalTypeRoute source color middle endpoint →
      CostCanonicalTypeRoute source color root endpoint
  | .refl => priorRoute
  | .parameter prior membership notBare parameterMembership parameterType =>
      .parameter (priorRoute.prepend prior) membership notBare
        parameterMembership parameterType
  | .codomain prior => .codomain (priorRoute.prepend prior)
  | .structuralCollectionElement prior =>
      .structuralCollectionElement (priorRoute.prepend prior)
  | .bareCollectionElement prior membership wrapped parameterShape =>
      .bareCollectionElement (priorRoute.prepend prior) membership wrapped
        parameterShape

/-- Rebase one reached-plan factorization through a larger skeleton context.
The reached plan, its binder fibres, and its inventory are unchanged. -/
def CostStaticPlanReached.rebaseAbstractRoot
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload childRoot outerRoot : Pattern}
    (reached : CostStaticPlanReached source color targetFree payload childRoot)
    (frame : OneHoleContext)
    (rootEq : outerRoot = frame.fill childRoot) :
    CostStaticPlanReached source color targetFree payload outerRoot :=
  { sourceBound := reached.sourceBound
    targetBound := reached.targetBound
    thinning := reached.thinning
    sourceAvailable := reached.sourceAvailable
    outer := reached.outer
    sourceType := reached.sourceType
    plan := reached.plan
    skeletonContext := frame.comp reached.skeletonContext
    abstract_eq := by
      rw [OneHoleContext.fill_comp]
      exact rootEq.trans (congrArg frame.fill reached.abstract_eq) }

/-- Rebase a child-root stop into a larger pair of plan roots while retaining
the strict measure supplied by the child position.  Entry embeddings, type
routes, and skeleton contexts compose proof-relevantly. -/
theorem CostStaticPlanCanonicalStop.liftBelow
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {outerSourceBound outerTargetBound childSourceBound childTargetBound :
      List TypeExpr}
    {outerThinning : CostStaticBinderThinning source color outerSourceBound
      outerTargetBound}
    {childThinning : CostStaticBinderThinning source color childSourceBound
      childTargetBound}
    {leftOuterAvailable rightOuterAvailable leftChildAvailable
      rightChildAvailable : List TypeExpr}
    {leftOuterContext rightOuterContext leftChildContext rightChildContext :
      OneHoleContext}
    {leftOuterRoot rightOuterRoot leftChildRoot rightChildRoot : Pattern}
    {outerSourceType childSourceType : TypeExpr}
    (leftOuterPlan : CostStaticRegionPlan source color targetFree
      outerSourceBound outerTargetBound outerThinning leftOuterAvailable
      leftOuterContext leftOuterRoot outerSourceType)
    (rightOuterPlan : CostStaticRegionPlan source color targetFree
      outerSourceBound outerTargetBound outerThinning rightOuterAvailable
      rightOuterContext rightOuterRoot outerSourceType)
    (leftChildPlan : CostStaticRegionPlan source color targetFree
      childSourceBound childTargetBound childThinning leftChildAvailable
      leftChildContext leftChildRoot childSourceType)
    (rightChildPlan : CostStaticRegionPlan source color targetFree
      childSourceBound childTargetBound childThinning rightChildAvailable
      rightChildContext rightChildRoot childSourceType)
    (leftFrame rightFrame : OneHoleContext)
    (leftRootEq : leftOuterPlan.abstractPattern =
      leftFrame.fill leftChildPlan.abstractPattern)
    (rightRootEq : rightOuterPlan.abstractPattern =
      rightFrame.fill rightChildPlan.abstractPattern)
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      leftChildPlan.boundaryTable.entries leftOuterPlan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      rightChildPlan.boundaryTable.entries rightOuterPlan.boundaryTable.entries)
    (leftRoute : Nonempty (CostCanonicalTypeRoute source color
      (mapTypeExpr (color.symbols source) outerSourceType)
      (mapTypeExpr (color.symbols source) childSourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute source color
      (mapTypeExpr (color.symbols source) outerSourceType)
      (mapTypeExpr (color.symbols source) childSourceType)))
    (leftChildLt : sizeOf leftChildRoot < sizeOf leftOuterRoot)
    (rightChildLt : sizeOf rightChildRoot < sizeOf rightOuterRoot)
    {declaration rawDeclaration : ReflectivePresentationDecl}
    {rawStop : Pattern → Pattern → Prop} {parentMeasure : Nat}
    {leftAbstract rightAbstract : Pattern}
    (parentMeasureEq : parentMeasure =
      sizeOf leftOuterRoot + sizeOf rightOuterRoot)
    (stopped : CostStaticPlanCanonicalStop leftChildPlan rightChildPlan
      declaration rawDeclaration rawStop leftAbstract rightAbstract) :
    CostStaticPlanCanonicalStopBelow leftOuterPlan rightOuterPlan declaration
      rawDeclaration rawStop parentMeasure leftAbstract rightAbstract := by
  rcases stopped with
    ⟨leftPayload, rightPayload, leftReached, rightReached, leftAdmission,
      rightAdmission, leftAbstractEq, rightAbstractEq, sourceTypeEq,
      sourceAvailableEq, sourceBoundEq, targetBoundEq, thinningEq,
      leftInnerEmbedding, rightInnerEmbedding, leftInnerRoute, rightInnerRoute,
      stopReason, leftSizeLe, rightSizeLe, rawAligned⟩
  let leftReached' := leftReached.rebaseAbstractRoot leftFrame leftRootEq
  let rightReached' := rightReached.rebaseAbstractRoot rightFrame rightRootEq
  rcases leftInnerEmbedding with ⟨leftInnerEmbedding⟩
  rcases rightInnerEmbedding with ⟨rightInnerEmbedding⟩
  rcases leftRoute with ⟨leftRoute⟩
  rcases rightRoute with ⟨rightRoute⟩
  rcases leftInnerRoute with ⟨leftInnerRoute⟩
  rcases rightInnerRoute with ⟨rightInnerRoute⟩
  refine ⟨leftPayload, rightPayload, ?_, ?_⟩
  · refine ⟨leftReached', rightReached', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ⟨leftInnerEmbedding.comp leftEmbedding⟩,
      ⟨rightInnerEmbedding.comp rightEmbedding⟩,
      ⟨leftRoute.prepend leftInnerRoute⟩,
      ⟨rightRoute.prepend rightInnerRoute⟩, ?_, ?_, ?_, rawAligned⟩
    · change leftReached.plan.RawAdmission
      exact leftAdmission
    · change rightReached.plan.RawAdmission
      exact rightAdmission
    · change leftReached.plan.abstractPattern = leftAbstract
      exact leftAbstractEq
    · change rightReached.plan.abstractPattern = rightAbstract
      exact rightAbstractEq
    · change leftReached.sourceType = rightReached.sourceType
      exact sourceTypeEq
    · change leftReached.sourceAvailable = rightReached.sourceAvailable
      exact sourceAvailableEq
    · change leftReached.sourceBound = rightReached.sourceBound
      exact sourceBoundEq
    · change leftReached.targetBound = rightReached.targetBound
      exact targetBoundEq
    · change HEq leftReached.thinning rightReached.thinning
      exact thinningEq
    · change rawStop leftPayload rightPayload ∨
        CostStaticPlanStopEligible declaration leftReached.plan
          rightReached.plan
      exact stopReason
    · omega
    · omega
  · omega

/-- Every provenance-bearing plan stop exposes raw payloads with equal
canonical forms whenever its delegated raw stops do.  The reached plans and
root-table embeddings remain available by eliminating the original stop;
this projection records only the equality needed by recursive consumers. -/
theorem CostStaticPlanCanonicalStop.exists_payload_canonicalize_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftSourceBound rightSourceBound leftTargetBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning source color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning source color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftRoot rightRoot : Pattern} {leftSourceType rightSourceType : TypeExpr}
    {leftPlan : CostStaticRegionPlan source color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftRoot
      leftSourceType}
    {rightPlan : CostStaticRegionPlan source color targetFree rightSourceBound
      rightTargetBound rightThinning rightAvailable rightOuter rightRoot
      rightSourceType}
    {declaration rawDeclaration : ReflectivePresentationDecl}
    {rawStop : Pattern → Pattern → Prop}
    {leftAbstract rightAbstract : Pattern}
    (stopped : CostStaticPlanCanonicalStop leftPlan rightPlan declaration
      rawDeclaration rawStop leftAbstract rightAbstract)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize rawDeclaration left = canonicalize rawDeclaration right) :
    ∃ leftPayload rightPayload,
      canonicalize rawDeclaration leftPayload =
        canonicalize rawDeclaration rightPayload := by
  rcases stopped with
    ⟨leftPayload, rightPayload, _leftReached, _rightReached,
      _leftAdmission, _rightAdmission,
      _leftAbstractEq, _rightAbstractEq, _sourceTypeEq, _sourceAvailableEq,
      _sourceBoundEq, _targetBoundEq, _thinningEq,
      _leftEmbedding, _rightEmbedding, _leftRoute, _rightRoute, _stopReason,
      _leftSizeLe, _rightSizeLe, rawAligned⟩
  exact ⟨leftPayload, rightPayload,
    rawAligned.canonicalize_eq rawDeclaration stopCanonical⟩

/-- Package one current plan pair as an exact root-inventory stop. -/
private theorem costStaticPlanCanonicalStop_of_reached
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftSourceBound rightSourceBound leftTargetBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning source color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning source color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftRoot rightRoot leftPayload rightPayload : Pattern}
    {leftSourceType rightSourceType leftPayloadType rightPayloadType :
      TypeExpr}
    (leftRootPlan : CostStaticRegionPlan source color targetFree
      leftSourceBound leftTargetBound leftThinning leftAvailable leftOuter
      leftRoot leftSourceType)
    (rightRootPlan : CostStaticRegionPlan source color targetFree
      rightSourceBound rightTargetBound rightThinning rightAvailable rightOuter
      rightRoot rightSourceType)
    {payloadSourceBound payloadTargetBound : List TypeExpr}
    {payloadThinning : CostStaticBinderThinning source color
      payloadSourceBound payloadTargetBound}
    {leftPayloadAvailable rightPayloadAvailable : List TypeExpr}
    {leftPayloadOuter rightPayloadOuter : OneHoleContext}
    (leftPayloadPlan : CostStaticRegionPlan source color targetFree
      payloadSourceBound payloadTargetBound payloadThinning
      leftPayloadAvailable leftPayloadOuter leftPayload leftPayloadType)
    (rightPayloadPlan : CostStaticRegionPlan source color targetFree
      payloadSourceBound payloadTargetBound payloadThinning
      rightPayloadAvailable rightPayloadOuter rightPayload rightPayloadType)
    (leftAdmission : leftPayloadPlan.RawAdmission)
    (rightAdmission : rightPayloadPlan.RawAdmission)
    (leftSkeletonContext rightSkeletonContext : OneHoleContext)
    (leftAbstractEq : leftRootPlan.abstractPattern =
      leftSkeletonContext.fill leftPayloadPlan.abstractPattern)
    (rightAbstractEq : rightRootPlan.abstractPattern =
      rightSkeletonContext.fill rightPayloadPlan.abstractPattern)
    (payloadTypeEq : leftPayloadType = rightPayloadType)
    (payloadAvailableEq : leftPayloadAvailable = rightPayloadAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      leftPayloadPlan.boundaryTable.entries
      leftRootPlan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      rightPayloadPlan.boundaryTable.entries
      rightRootPlan.boundaryTable.entries)
    (leftRoute : Nonempty (CostCanonicalTypeRoute source color
      (mapTypeExpr (color.symbols source) leftSourceType)
      (mapTypeExpr (color.symbols source) leftPayloadType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute source color
      (mapTypeExpr (color.symbols source) rightSourceType)
      (mapTypeExpr (color.symbols source) rightPayloadType)))
    (leftSizeLe : sizeOf leftPayload ≤ sizeOf leftRoot)
    (rightSizeLe : sizeOf rightPayload ≤ sizeOf rightRoot)
    {declaration rawDeclaration : ReflectivePresentationDecl}
    {rawStop : Pattern → Pattern → Prop}
    (stopReason : rawStop leftPayload rightPayload ∨
      CostStaticPlanStopEligible declaration leftPayloadPlan rightPayloadPlan)
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
      rightPayload) :
    CostStaticPlanCanonicalStop leftRootPlan rightRootPlan declaration
      rawDeclaration rawStop leftPayloadPlan.abstractPattern
        rightPayloadPlan.abstractPattern := by
  let leftReached : CostStaticPlanReached source color targetFree leftPayload
      leftRootPlan.abstractPattern :=
    { sourceBound := payloadSourceBound
      targetBound := payloadTargetBound
      thinning := payloadThinning
      sourceAvailable := leftPayloadAvailable
      outer := leftPayloadOuter
      sourceType := leftPayloadType
      plan := leftPayloadPlan
      skeletonContext := leftSkeletonContext
      abstract_eq := leftAbstractEq }
  let rightReached : CostStaticPlanReached source color targetFree rightPayload
      rightRootPlan.abstractPattern :=
    { sourceBound := payloadSourceBound
      targetBound := payloadTargetBound
      thinning := payloadThinning
      sourceAvailable := rightPayloadAvailable
      outer := rightPayloadOuter
      sourceType := rightPayloadType
      plan := rightPayloadPlan
      skeletonContext := rightSkeletonContext
      abstract_eq := rightAbstractEq }
  refine ⟨leftPayload, rightPayload, leftReached, rightReached, ?_, ?_, rfl,
    rfl, ?_, ?_, rfl, rfl, HEq.rfl, ?_, ?_, leftRoute, rightRoute, ?_,
      leftSizeLe, rightSizeLe, rawAligned⟩
  · simpa [leftReached] using leftAdmission
  · simpa [rightReached] using rightAdmission
  · simpa [leftReached, rightReached] using payloadTypeEq
  · simpa [leftReached, rightReached] using payloadAvailableEq
  · exact ⟨leftEmbedding⟩
  · exact ⟨rightEmbedding⟩
  · simpa [leftReached, rightReached] using stopReason

/-- Reindex only the homogeneous element fibre of an element plan.  No raw
element, occurrence position, or boundary table is changed. -/
def CostStaticElementPlan.castSourceElementType
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {before elements : List Pattern}
    {rest : Option String} {first second : TypeExpr}
    (equal : first = second)
    (plan : CostStaticElementPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer collectionType before
      elements rest second) :
    CostStaticElementPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer collectionType before elements rest
      first := by
  cases equal
  exact plan

@[simp]
theorem CostStaticElementPlan.abstractPatterns_castSourceElementType
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {before elements : List Pattern}
    {rest : Option String} {first second : TypeExpr}
    (equal : first = second)
    (plan : CostStaticElementPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer collectionType before
      elements rest second) :
    (plan.castSourceElementType equal).abstractPatterns =
      plan.abstractPatterns := by
  cases equal
  rfl

@[simp]
theorem CostStaticElementPlan.boundaryTable_entries_castSourceElementType
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {before elements : List Pattern}
    {rest : Option String} {first second : TypeExpr}
    (equal : first = second)
    (plan : CostStaticElementPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer collectionType before
      elements rest second) :
    (plan.castSourceElementType equal).boundaryTable.entries =
      plan.boundaryTable.entries := by
  cases equal
  rfl

/-- Reindex an argument plan by equality of its authored parameter spine.
The proof-relevant plan and all retained boundary positions stay unchanged. -/
private def CostStaticArgumentPlan.castParameters
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {wireName : String} {before arguments : List Pattern}
    {first second : List TermParam}
    (equal : first = second)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName before arguments
      second) :
    CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer wireName before arguments first := by
  cases equal
  exact plan

@[simp]
private theorem CostStaticArgumentPlan.abstractPatterns_castParameters
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {wireName : String} {before arguments : List Pattern}
    {first second : List TermParam}
    (equal : first = second)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName before arguments
      second) :
    (plan.castParameters equal).abstractPatterns = plan.abstractPatterns := by
  cases equal
  rfl

@[simp]
private theorem CostStaticArgumentPlan.boundaryTable_entries_castParameters
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {wireName : String} {before arguments : List Pattern}
    {first second : List TermParam}
    (equal : first = second)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName before arguments
      second) :
    (plan.castParameters equal).boundaryTable.entries =
      plan.boundaryTable.entries := by
  cases equal
  rfl

/-- Project the left chronological segment of an embedded appended table. -/
private def CostStaticPlanEntryEmbedding.leftOfTableAppend
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    (left : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences)
    (right : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences)
    {large : List (TypedCostRegionBoundary source color targetFree)}
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      (TypedCostRegionBoundaryTable.append left right).entries large) :
    CostStaticPlanEntryEmbedding source color targetFree left.entries large :=
  (CostStaticPlanEntryEmbedding.appendLeft left.entries right.entries).comp
    (by
      rw [← TypedCostRegionBoundaryTable.entries_append]
      exact embedding)

/-- Project the right chronological segment of an embedded appended table. -/
private def CostStaticPlanEntryEmbedding.rightOfTableAppend
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    (left : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences)
    (right : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences)
    {large : List (TypedCostRegionBoundary source color targetFree)}
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      (TypedCostRegionBoundaryTable.append left right).entries large) :
    CostStaticPlanEntryEmbedding source color targetFree right.entries large :=
  (CostStaticPlanEntryEmbedding.appendRight left.entries right.entries).comp
    (by
      rw [← TypedCostRegionBoundaryTable.entries_append]
      exact embedding)

/-- A selected collection typing choice advances the proof-relevant type
route to the exact element fibre retained by that choice.  Direct collection
typing records structural descent; bare collection typing retains the
authored declaration that justifies its language-specific interpretation. -/
theorem costCanonicalTypeRoute_of_collectionChoice
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {collectionType : CollType} {elements : List Pattern}
    {root expected : TypeExpr} {choice : CostCollectionTypingChoice}
    (selected : choice ∈ costStaticCollectionTypingChoices source color
      targetFree targetBound collectionType elements expected)
    (prior : Nonempty (CostCanonicalTypeRoute source color root expected)) :
    Nonempty (CostCanonicalTypeRoute source color root
      (mapTypeExpr (color.symbols source) choice.sourceElementType)) := by
  rcases prior with ⟨prior⟩
  rcases mem_costStaticCollectionTypingChoices_sound source color targetFree
      targetBound collectionType elements expected choice selected with
    direct | bare
  · rcases direct with
      ⟨sourceElementType, choiceEq, expectedEq, _elementsChecked⟩
    subst choice
    exact ⟨.structuralCollectionElement (prior.castEndpoint expectedEq)⟩
  · rcases bare with
      ⟨rule, sourceElementType, choiceEq, membership, wrapped, expectedEq,
        parameterName, parameterShape, _elementsChecked⟩
    subst choice
    exact ⟨.bareCollectionElement (prior.castEndpoint expectedEq) membership
      wrapped parameterShape⟩

/-! ## Lockstep transport -/

/-- The head of a reflectively safe pattern list is safe at the same depth. -/
private theorem reflectiveScopeSafeAt_cons_head
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {depth : Nat}
    {head : Pattern} {tail : List Pattern}
    (safe : ∀ presentation ∈ profile.presentations,
      binderSafeListAt presentation.quoteConstructor depth (head :: tail) =
        true) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt profile depth head := by
  intro presentation membership
  have spine := safe presentation membership
  simp only [binderSafeListAt, Bool.and_eq_true] at spine
  exact spine.1

/-- The tail of a reflectively safe pattern list is safe at the same depth. -/
private theorem binderSafeListAt_cons_tail
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {depth : Nat}
    {head : Pattern} {tail : List Pattern}
    (safe : ∀ presentation ∈ profile.presentations,
      binderSafeListAt presentation.quoteConstructor depth (head :: tail) =
        true) :
    ∀ presentation ∈ profile.presentations,
      binderSafeListAt presentation.quoteConstructor depth tail = true := by
  intro presentation membership
  have spine := safe presentation membership
  simp only [binderSafeListAt, Bool.and_eq_true] at spine
  exact spine.2

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
mutual
  /-- Transport a generated-pattern canonical descent through two exact
  static plans.  The recursive indices are shared observable fibres; the two
  proof-relevant plans and boundary inventories remain independent. -/
  theorem costStaticRegionPlan_canonicalStopAligned
      {source : CIGSLT} {color : CostStaticColor}
      (collectionDeterministic : CollectionChoiceDeterministic
        source.theory.presentation.presentation.language)
      (declaration : ReflectivePresentationDecl)
      (rawDeclaration : ReflectivePresentationDecl)
      {targetFree : WellSorted.FreeTypeContext}
      {rootSourceBound rootTargetBound : List TypeExpr}
      {rootThinning : CostStaticBinderThinning source color rootSourceBound
        rootTargetBound}
      {leftRootAvailable rightRootAvailable : List TypeExpr}
      {leftRootOuter rightRootOuter : OneHoleContext}
      {leftRoot rightRoot : Pattern} {rootSourceType : TypeExpr}
      (leftRootPlan : CostStaticRegionPlan source color targetFree
        rootSourceBound rootTargetBound rootThinning leftRootAvailable
        leftRootOuter leftRoot rootSourceType)
      (rightRootPlan : CostStaticRegionPlan source color targetFree
        rootSourceBound rootTargetBound rootThinning rightRootAvailable
        rightRootOuter rightRoot rootSourceType)
      {rawStop : Pattern → Pattern → Prop}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {leftAvailable rightAvailable : List TypeExpr}
      {leftOuter rightOuter : OneHoleContext}
      {leftPattern rightPattern : Pattern}
      {leftSourceType rightSourceType : TypeExpr}
      (leftPlan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning leftAvailable leftOuter leftPattern leftSourceType)
      (rightPlan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning rightAvailable rightOuter rightPattern
        rightSourceType)
      (leftAdmission : leftPlan.RawAdmission)
      (rightAdmission : rightPlan.RawAdmission)
      (leftSkeletonContext rightSkeletonContext : OneHoleContext)
      (leftAbstractEq : leftRootPlan.abstractPattern =
        leftSkeletonContext.fill leftPlan.abstractPattern)
      (rightAbstractEq : rightRootPlan.abstractPattern =
        rightSkeletonContext.fill rightPlan.abstractPattern)
      (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
        leftPlan.boundaryTable.entries leftRootPlan.boundaryTable.entries)
      (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
        rightPlan.boundaryTable.entries rightRootPlan.boundaryTable.entries)
      (leftRoute : Nonempty (CostCanonicalTypeRoute source color
        (mapTypeExpr (color.symbols source) rootSourceType)
        (mapTypeExpr (color.symbols source) leftSourceType)))
      (rightRoute : Nonempty (CostCanonicalTypeRoute source color
        (mapTypeExpr (color.symbols source) rootSourceType)
        (mapTypeExpr (color.symbols source) rightSourceType)))
      (sourceTypeEq : leftSourceType = rightSourceType)
      (availableEq : leftAvailable = rightAvailable)
      (leftSizeLe : sizeOf leftPattern ≤ sizeOf leftRoot)
      (rightSizeLe : sizeOf rightPattern ≤ sizeOf rightRoot)
      (rawAligned : CanonicalStopAligned
        rawDeclaration
        rawStop leftPattern rightPattern) :
      CanonicalStopAligned declaration
        (CostStaticPlanCanonicalStop leftRootPlan rightRootPlan declaration
          rawDeclaration
          rawStop)
        leftPlan.abstractPattern rightPlan.abstractPattern := by
    cases rawAligned with
    | leaf given =>
        exact .leaf (costStaticPlanCanonicalStop_of_reached leftRootPlan
          rightRootPlan leftPlan rightPlan leftAdmission rightAdmission
          leftSkeletonContext
          rightSkeletonContext leftAbstractEq rightAbstractEq sourceTypeEq
          availableEq leftEmbedding rightEmbedding leftRoute rightRoute
          leftSizeLe rightSizeLe
          (Or.inl given) (.leaf given))
    | bvar targetIndex =>
        cases leftPlan with
        | bvar leftSourceIndex leftLookup leftCorrespondence
            leftAvailableScope =>
          cases rightPlan with
          | bvar rightSourceIndex rightLookup rightCorrespondence
              rightAvailableScope =>
            have sourceIndexEq : leftSourceIndex = rightSourceIndex :=
              Option.some.inj
                (leftCorrespondence.symm.trans rightCorrespondence)
            subst rightSourceIndex
            exact .bvar leftSourceIndex
    | fvar name =>
        cases leftPlan with
        | fvar leftLookup =>
          cases rightPlan with
          | fvar rightLookup => exact .fvar (costRegionSourceVariableName name)
    | @apply wireName rawNe leftArguments rightArguments argumentsAligned =>
        cases leftPlan with
        | boundaryApplication leftConstructor leftRendered leftOutside
            leftCertified leftCertifies =>
          cases rightPlan with
          | boundaryApplication rightConstructor rightRendered rightOutside
              rightCertified rightCertifies =>
            exact .leaf (costStaticPlanCanonicalStop_of_reached leftRootPlan
              rightRootPlan
              (.boundaryApplication leftConstructor leftRendered leftOutside
                leftCertified leftCertifies)
              (.boundaryApplication rightConstructor rightRendered
                rightOutside rightCertified rightCertifies)
              leftAdmission rightAdmission
              leftSkeletonContext rightSkeletonContext leftAbstractEq
              rightAbstractEq sourceTypeEq availableEq leftEmbedding rightEmbedding
              leftRoute rightRoute
              leftSizeLe rightSizeLe
              (Or.inr (by
                simp [CostStaticPlanStopEligible,
                  CostStaticRegionPlan.rootClass]))
              (.apply rawNe argumentsAligned))
          | application rightConstructor rightRendered rightCurrent
              rightPreimage rightNotBare rightChildren =>
            have constructorEq : leftConstructor = rightConstructor :=
              source.renderDeclaredCostConstructor_injective
                (leftRendered.trans rightRendered.symm)
            subst rightConstructor
            exact (leftOutside rightCurrent).elim
        | application leftConstructor leftRendered leftCurrent leftPreimage
            leftNotBare leftChildren =>
          cases rightPlan with
          | boundaryApplication rightConstructor rightRendered rightOutside
              rightCertified rightCertifies =>
            have constructorEq : leftConstructor = rightConstructor :=
              source.renderDeclaredCostConstructor_injective
                (leftRendered.trans rightRendered.symm)
            subst rightConstructor
            exact (rightOutside leftCurrent).elim
          | application rightConstructor rightRendered rightCurrent
              rightPreimage rightNotBare rightChildren =>
            have constructorEq : leftConstructor = rightConstructor :=
              source.renderDeclaredCostConstructor_injective
                (leftRendered.trans rightRendered.symm)
            subst rightConstructor
            by_cases sourceNe :
                leftPreimage.sourceConstructor.1.label ≠
                  declaration.quoteConstructor
            · have preimageEq : leftPreimage = rightPreimage :=
                CostStaticConstructorPreimage.eq _ _
              subst rightPreimage
              subst rightAvailable
              obtain ⟨targetRule, targetMembership, targetLabel, _targetNotBare,
                  _targetType, leftArgumentsTypedAtParent,
                  rightArgumentsTypedAtParent⟩ :=
                hasType_apply_pair source.costWholeLanguage_labelDeterministic
                  leftAdmission.wellSorted.1.1
                  rightAdmission.wellSorted.1.1
              have materializedMembership :
                  source.materializeDeclaredCostConstructor leftConstructor ∈
                    source.costWholeLanguage.terms := by
                simpa only [source.costWholeLanguage_terms] using
                  source.materializeDeclaredCostConstructor_mem leftConstructor
              have targetRuleEq : targetRule =
                  source.materializeDeclaredCostConstructor leftConstructor :=
                source.costWholeLanguage_labelDeterministic targetMembership
                  materializedMembership
                  (targetLabel.symm.trans
                    ((source.materializeDeclaredCostConstructor_label
                      leftConstructor).trans leftRendered).symm)
              subst targetRule
              have leftArgumentsTypedForQuote := leftArgumentsTypedAtParent
              have rightArgumentsTypedForQuote := rightArgumentsTypedAtParent
              rw [leftPreimage.parametersMap] at leftArgumentsTypedAtParent
              rw [leftPreimage.parametersMap] at rightArgumentsTypedAtParent
              have leftCanonicalArguments :
                  Pattern.hasCanonicalBinderMetadataList leftArguments = true := by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  leftAdmission.wellSorted.1.2.1
              have rightCanonicalArguments :
                  Pattern.hasCanonicalBinderMetadataList rightArguments = true := by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  rightAdmission.wellSorted.1.2.1
              have leftObjectArguments :
                  WellSorted.isObjectPatternList leftArguments = true := by
                simpa [WellSorted.isObjectPattern] using
                  leftAdmission.wellSorted.1.2.2.1
              have rightObjectArguments :
                  WellSorted.isObjectPatternList rightArguments = true := by
                simpa [WellSorted.isObjectPattern] using
                  rightAdmission.wellSorted.1.2.2.1
              have leftParentReflective :
                  ReflectiveWellSorted.ReflectiveScopeSafeAt
                    source.costWholeReflectionProfile leftAvailable.length
                    (.apply
                      (source.materializeDeclaredCostConstructor
                        leftConstructor).label leftArguments) := by
                simpa only [source.materializeDeclaredCostConstructor_label,
                  leftRendered] using leftAdmission.wellSorted.2
              have rightParentReflective :
                  ReflectiveWellSorted.ReflectiveScopeSafeAt
                    source.costWholeReflectionProfile leftAvailable.length
                    (.apply
                      (source.materializeDeclaredCostConstructor
                        leftConstructor).label rightArguments) := by
                simpa only [source.materializeDeclaredCostConstructor_label,
                  rightRendered] using rightAdmission.wellSorted.2
              have parameterRoute :
                  ∀ {parameter : TermParam} {expected : TypeExpr},
                    parameter ∈ leftPreimage.sourceConstructor.1.params →
                    parameterType? parameter = some expected →
                      Nonempty (CostCanonicalTypeRoute source color
                        (mapTypeExpr (color.symbols source) rootSourceType)
                        (mapTypeExpr (color.symbols source) expected)) := by
                intro parameter expected parameterMembership parameterTyped
                rcases leftRoute with ⟨leftRoute⟩
                have prior : CostCanonicalTypeRoute source color
                    (mapTypeExpr (color.symbols source) rootSourceType)
                    (.base
                      (source.materializeDeclaredCostConstructor
                        leftConstructor).category) :=
                  leftRoute.castEndpoint (by
                    simpa [mapTypeExpr] using congrArg TypeExpr.base
                      leftPreimage.categoryMap.symm)
                refine ⟨CostCanonicalTypeRoute.parameter
                  (parameter := mapTermParam (color.symbols source) parameter)
                  prior ?_ ?_ ?_ ?_⟩
                · simpa only [source.costWholeLanguage_terms] using
                    source.materializeDeclaredCostConstructor_mem
                      leftConstructor
                · intro targetBare
                  exact leftNotBare
                    (leftPreimage.source_usesBareCollection leftCurrent
                      targetBare)
                · rw [leftPreimage.parametersMap]
                  exact List.mem_map_of_mem parameterMembership
                · simp [WellSorted.parameterType?_mapTermParam,
                    parameterTyped]
              by_cases sourceQuoted :
                  ReflectiveContextSupport.isQuoteConstructor
                    source.reflection.1
                    leftPreimage.sourceConstructor.1.label = true
              · have targetQuoted :
                    ReflectiveContextSupport.isQuoteConstructor
                      source.costWholeReflectionProfile
                      (source.materializeDeclaredCostConstructor
                        leftConstructor).label = true := by
                  rw [leftPreimage.labelMap]
                  simpa only [reflectiveIsQuoteConstructor_mapCostStatic] using
                    sourceQuoted
                have leftAtZero :=
                  WellSorted.isWellScopedListAt_zero_of_typed_quote
                    source.costWholeLanguage_validate
                    source.costWholeReflectionProfile_validate
                    materializedMembership leftArgumentsTypedForQuote
                    targetQuoted leftParentReflective
                have rightAtZero :=
                  WellSorted.isWellScopedListAt_zero_of_typed_quote
                    source.costWholeLanguage_validate
                    source.costWholeReflectionProfile_validate
                    materializedMembership rightArgumentsTypedForQuote
                    targetQuoted rightParentReflective
                have leftArgumentsTyped : WellSorted.ArgumentsHaveTypes
                    source.costWholeLanguage targetFree [] leftArguments
                    (leftPreimage.sourceConstructor.1.params.map
                      (mapTermParam (color.symbols source))) := by
                  exact leftArgumentsTypedAtParent.restrictOuterOfScoped
                    (inner := []) (outer := leftAvailable) leftAtZero
                have rightArgumentsTyped : WellSorted.ArgumentsHaveTypes
                    source.costWholeLanguage targetFree [] rightArguments
                    (leftPreimage.sourceConstructor.1.params.map
                      (mapTermParam (color.symbols source))) := by
                  exact rightArgumentsTypedAtParent.restrictOuterOfScoped
                    (inner := []) (outer := leftAvailable) rightAtZero
                have leftReflective :=
                  WellSorted.reflectiveScopeSafeListAt_zero_of_typed_quote
                    source.costWholeLanguage_validate
                    source.costWholeReflectionProfile_validate
                    materializedMembership leftArgumentsTypedForQuote
                    targetQuoted leftParentReflective
                have rightReflective :=
                  WellSorted.reflectiveScopeSafeListAt_zero_of_typed_quote
                    source.costWholeLanguage_validate
                    source.costWholeReflectionProfile_validate
                    materializedMembership rightArgumentsTypedForQuote
                    targetQuoted rightParentReflective
                have childrenAligned :=
                  costStaticArgumentPlan_canonicalStopAligned
                    collectionDeterministic declaration rawDeclaration
                    leftRootPlan rightRootPlan
                    leftPreimage.sourceConstructor.1.label [] [] leftChildren
                    rightChildren
                    (by simpa [sourceQuoted] using leftArgumentsTyped)
                    (by simpa [sourceQuoted] using rightArgumentsTyped)
                    leftCanonicalArguments rightCanonicalArguments
                    leftObjectArguments rightObjectArguments
                    (by simpa [sourceQuoted] using leftReflective)
                    (by simpa [sourceQuoted] using rightReflective)
                    ⟨targetBound, by simp [sourceQuoted]⟩
                    ⟨targetBound, by simp [sourceQuoted]⟩
                    leftSkeletonContext rightSkeletonContext
                    (by simpa [CostStaticRegionPlan.abstractPattern] using
                      leftAbstractEq)
                    (by simpa [CostStaticRegionPlan.abstractPattern] using
                      rightAbstractEq)
                    (by
                      change CostStaticPlanEntryEmbedding source color targetFree
                        leftChildren.boundaryTable.entries
                        leftRootPlan.boundaryTable.entries at leftEmbedding
                      exact leftEmbedding)
                    (by
                      change CostStaticPlanEntryEmbedding source color targetFree
                        rightChildren.boundaryTable.entries
                        rightRootPlan.boundaryTable.entries at rightEmbedding
                      exact rightEmbedding)
                    (fun parameterMembership parameterTyped =>
                      parameterRoute parameterMembership parameterTyped)
                    rfl
                    (by simp at leftSizeLe ⊢; omega)
                    (by simp at rightSizeLe ⊢; omega)
                    argumentsAligned
                simpa [CostStaticRegionPlan.abstractPattern] using
                  (CanonicalStopAligned.apply sourceNe childrenAligned)
              · have sourceOrdinary :
                    ReflectiveContextSupport.isQuoteConstructor
                      source.reflection.1
                      leftPreimage.sourceConstructor.1.label = false :=
                  Bool.eq_false_of_not_eq_true sourceQuoted
                have targetOrdinary :
                    ReflectiveContextSupport.isQuoteConstructor
                      source.costWholeReflectionProfile
                      (source.materializeDeclaredCostConstructor
                        leftConstructor).label = false := by
                  rw [leftPreimage.labelMap]
                  simpa only [reflectiveIsQuoteConstructor_mapCostStatic] using
                    sourceOrdinary
                have leftReflective :=
                  WellSorted.reflectiveScopeSafeListAt_of_nonquote
                    targetOrdinary leftParentReflective
                have rightReflective :=
                  WellSorted.reflectiveScopeSafeListAt_of_nonquote
                    targetOrdinary rightParentReflective
                have childrenAligned :=
                  costStaticArgumentPlan_canonicalStopAligned
                  collectionDeterministic declaration rawDeclaration
                  leftRootPlan rightRootPlan
                  leftPreimage.sourceConstructor.1.label [] [] leftChildren
                  rightChildren
                  (by simpa [sourceQuoted] using leftArgumentsTypedAtParent)
                  (by simpa [sourceQuoted] using rightArgumentsTypedAtParent)
                  leftCanonicalArguments
                    rightCanonicalArguments leftObjectArguments
                    rightObjectArguments
                    (by simpa [sourceQuoted] using leftReflective)
                    (by simpa [sourceQuoted] using rightReflective)
                    (by simpa [sourceQuoted] using
                      leftAdmission.targetBound_split)
                    (by simpa [sourceQuoted] using
                      rightAdmission.targetBound_split)
                    leftSkeletonContext rightSkeletonContext
                    (by simpa [CostStaticRegionPlan.abstractPattern] using
                      leftAbstractEq)
                    (by simpa [CostStaticRegionPlan.abstractPattern] using
                      rightAbstractEq)
                    (by
                      change CostStaticPlanEntryEmbedding source color targetFree
                        leftChildren.boundaryTable.entries
                        leftRootPlan.boundaryTable.entries at leftEmbedding
                      exact leftEmbedding)
                    (by
                      change CostStaticPlanEntryEmbedding source color targetFree
                        rightChildren.boundaryTable.entries
                        rightRootPlan.boundaryTable.entries at rightEmbedding
                      exact rightEmbedding)
                  parameterRoute
                  rfl
                  (by simp at leftSizeLe ⊢; omega)
                  (by simp at rightSizeLe ⊢; omega)
                  argumentsAligned
                simpa [CostStaticRegionPlan.abstractPattern] using
                  (CanonicalStopAligned.apply sourceNe childrenAligned)
            · exact .leaf (costStaticPlanCanonicalStop_of_reached leftRootPlan
                rightRootPlan
                (.application leftConstructor leftRendered leftCurrent
                  leftPreimage leftNotBare leftChildren)
                (.application leftConstructor rightRendered rightCurrent
                  rightPreimage rightNotBare rightChildren)
                leftAdmission rightAdmission
                leftSkeletonContext rightSkeletonContext leftAbstractEq
                rightAbstractEq sourceTypeEq availableEq leftEmbedding
                rightEmbedding leftRoute rightRoute
                leftSizeLe rightSizeLe
                (Or.inr (by
                  have preimageEq : leftPreimage = rightPreimage :=
                    CostStaticConstructorPreimage.eq _ _
                  subst rightPreimage
                  simp at sourceNe
                  simpa [CostStaticPlanStopEligible,
                    CostStaticRegionPlan.rootClass] using
                    And.intro sourceNe sourceNe))
                (.apply rawNe argumentsAligned))
    | @lambda binder leftBody rightBody bodyAligned =>
        cases leftPlan with
        | lambda leftBodyPlan =>
          cases rightPlan with
          | lambda rightBodyPlan =>
            injection sourceTypeEq with domainEq codomainEq
            cases domainEq
            cases codomainEq
            have leftBodyAdmission : leftBodyPlan.RawAdmission := by
              have leftBodyTyped := by
                cases leftAdmission.wellSorted.1.1 with
                | lambda bodyTyped => exact bodyTyped
              have canonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  leftAdmission.wellSorted.1.2.1 :
                    binder.isNone = true ∧
                      leftBody.hasCanonicalBinderMetadata = true)
              have bodyObject : WellSorted.isObjectPattern leftBody = true := by
                simpa [WellSorted.isObjectPattern] using
                  leftAdmission.wellSorted.1.2.2.1
              obtain ⟨sealed, split⟩ := leftAdmission.targetBound_split
              refine ⟨⟨⟨leftBodyTyped, canonicalParts.2, bodyObject,
                leftBodyTyped.isWellScopedAt⟩, ?_⟩, ⟨sealed, ?_⟩⟩
              · intro presentation membership
                have parent := leftAdmission.wellSorted.2 presentation
                  membership
                simpa [binderSafeAt, Nat.add_comm] using parent
              · simp [split]
            have rightBodyAdmission : rightBodyPlan.RawAdmission := by
              have rightBodyTyped := by
                cases rightAdmission.wellSorted.1.1 with
                | lambda bodyTyped => exact bodyTyped
              have canonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  rightAdmission.wellSorted.1.2.1 :
                    binder.isNone = true ∧
                      rightBody.hasCanonicalBinderMetadata = true)
              have bodyObject : WellSorted.isObjectPattern rightBody = true := by
                simpa [WellSorted.isObjectPattern] using
                  rightAdmission.wellSorted.1.2.2.1
              obtain ⟨sealed, split⟩ := rightAdmission.targetBound_split
              refine ⟨⟨⟨rightBodyTyped, canonicalParts.2, bodyObject,
                rightBodyTyped.isWellScopedAt⟩, ?_⟩, ⟨sealed, ?_⟩⟩
              · intro presentation membership
                have parent := rightAdmission.wellSorted.2 presentation
                  membership
                simpa [binderSafeAt, Nat.add_comm] using parent
              · simp [split]
            let leftFrame : OneHoleContext := .lambda binder .hole
            let rightFrame : OneHoleContext := .lambda binder .hole
            exact .lambda binder
              (costStaticRegionPlan_canonicalStopAligned
                collectionDeterministic declaration rawDeclaration
                leftRootPlan rightRootPlan
                leftBodyPlan rightBodyPlan
                leftBodyAdmission rightBodyAdmission
                (leftSkeletonContext.comp leftFrame)
                (rightSkeletonContext.comp rightFrame)
                (by
                  rw [OneHoleContext.fill_comp]
                  simpa [leftFrame, OneHoleContext.fill,
                    CostStaticRegionPlan.abstractPattern] using leftAbstractEq)
                (by
                  rw [OneHoleContext.fill_comp]
                  simpa [rightFrame, OneHoleContext.fill,
                    CostStaticRegionPlan.abstractPattern] using rightAbstractEq)
                (by
                  change CostStaticPlanEntryEmbedding source color targetFree
                    leftBodyPlan.boundaryTable.entries
                    leftRootPlan.boundaryTable.entries at leftEmbedding
                  exact leftEmbedding)
                (by
                  change CostStaticPlanEntryEmbedding source color targetFree
                    rightBodyPlan.boundaryTable.entries
                    rightRootPlan.boundaryTable.entries at rightEmbedding
                  exact rightEmbedding)
                (leftRoute.map CostCanonicalTypeRoute.codomain)
                (rightRoute.map CostCanonicalTypeRoute.codomain)
                rfl
                (congrArg
                  (fun tail => _ :: tail)
                  availableEq)
                (by simp at leftSizeLe ⊢; omega)
                (by simp at rightSizeLe ⊢; omega)
                bodyAligned)
    | @multiLambda arity binders leftBody rightBody bodyAligned =>
        cases leftPlan with
        | multiLambda leftBodyPlan =>
          cases rightPlan with
          | multiLambda rightBodyPlan =>
            injection sourceTypeEq with domainEq codomainEq
            cases domainEq
            cases codomainEq
            have leftBodyAdmission : leftBodyPlan.RawAdmission := by
              have leftBodyTyped := by
                cases leftAdmission.wellSorted.1.1 with
                | multiLambda bodyTyped => exact bodyTyped
              have canonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  leftAdmission.wellSorted.1.2.1 :
                    binders.isEmpty = true ∧
                      leftBody.hasCanonicalBinderMetadata = true)
              have bodyObject : WellSorted.isObjectPattern leftBody = true := by
                simpa [WellSorted.isObjectPattern] using
                  leftAdmission.wellSorted.1.2.2.1
              obtain ⟨sealed, split⟩ := leftAdmission.targetBound_split
              refine ⟨⟨⟨leftBodyTyped, canonicalParts.2, bodyObject,
                leftBodyTyped.isWellScopedAt⟩, ?_⟩, ⟨sealed, ?_⟩⟩
              · intro presentation membership
                have parent := leftAdmission.wellSorted.2 presentation
                  membership
                simpa [binderSafeAt, List.length_append,
                  List.length_replicate, Nat.add_comm, Nat.add_left_comm,
                  Nat.add_assoc] using parent
              · simp [split, List.append_assoc]
            have rightBodyAdmission : rightBodyPlan.RawAdmission := by
              have rightBodyTyped := by
                cases rightAdmission.wellSorted.1.1 with
                | multiLambda bodyTyped => exact bodyTyped
              have canonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  rightAdmission.wellSorted.1.2.1 :
                    binders.isEmpty = true ∧
                      rightBody.hasCanonicalBinderMetadata = true)
              have bodyObject : WellSorted.isObjectPattern rightBody = true := by
                simpa [WellSorted.isObjectPattern] using
                  rightAdmission.wellSorted.1.2.2.1
              obtain ⟨sealed, split⟩ := rightAdmission.targetBound_split
              refine ⟨⟨⟨rightBodyTyped, canonicalParts.2, bodyObject,
                rightBodyTyped.isWellScopedAt⟩, ?_⟩, ⟨sealed, ?_⟩⟩
              · intro presentation membership
                have parent := rightAdmission.wellSorted.2 presentation
                  membership
                simpa [binderSafeAt, List.length_append,
                  List.length_replicate, Nat.add_comm, Nat.add_left_comm,
                  Nat.add_assoc] using parent
              · simp [split, List.append_assoc]
            let leftFrame : OneHoleContext :=
              .multiLambda arity binders .hole
            let rightFrame : OneHoleContext :=
              .multiLambda arity binders .hole
            exact .multiLambda arity binders
              (costStaticRegionPlan_canonicalStopAligned
                collectionDeterministic declaration rawDeclaration
                leftRootPlan rightRootPlan
                leftBodyPlan rightBodyPlan
                leftBodyAdmission rightBodyAdmission
                (leftSkeletonContext.comp leftFrame)
                (rightSkeletonContext.comp rightFrame)
                (by
                  rw [OneHoleContext.fill_comp]
                  simpa [leftFrame, OneHoleContext.fill,
                    CostStaticRegionPlan.abstractPattern] using leftAbstractEq)
                (by
                  rw [OneHoleContext.fill_comp]
                  simpa [rightFrame, OneHoleContext.fill,
                    CostStaticRegionPlan.abstractPattern] using rightAbstractEq)
                (by
                  change CostStaticPlanEntryEmbedding source color targetFree
                    leftBodyPlan.boundaryTable.entries
                    leftRootPlan.boundaryTable.entries at leftEmbedding
                  exact leftEmbedding)
                (by
                  change CostStaticPlanEntryEmbedding source color targetFree
                    rightBodyPlan.boundaryTable.entries
                    rightRootPlan.boundaryTable.entries at rightEmbedding
                  exact rightEmbedding)
                (leftRoute.map CostCanonicalTypeRoute.codomain)
                (rightRoute.map CostCanonicalTypeRoute.codomain)
                rfl
                (congrArg
                  (fun available => _ ++ available)
                  availableEq)
                (by simp at leftSizeLe ⊢; omega)
                (by simp at rightSizeLe ⊢; omega)
                bodyAligned)
    | subst bodyAligned replacementAligned =>
        cases leftPlan
    | @collection collectionType rawNe leftElements rightElements
        elementsAligned =>
        cases leftPlan with
        | boundaryCollection leftRejected leftOpposite leftOppositeSelected
            leftCertified leftCertifies =>
          exact .leaf (costStaticPlanCanonicalStop_of_reached leftRootPlan
            rightRootPlan _ rightPlan leftAdmission rightAdmission
            leftSkeletonContext
            rightSkeletonContext leftAbstractEq rightAbstractEq sourceTypeEq
            availableEq leftEmbedding rightEmbedding leftRoute rightRoute
            leftSizeLe rightSizeLe
            (Or.inr (by
              cases rightPlan <;>
                simp [CostStaticPlanStopEligible,
                  CostStaticRegionPlan.rootClass]))
            (.collection rawNe elementsAligned))
        | collection leftChoice leftSelected leftChildren =>
          cases rightPlan with
          | boundaryCollection rightRejected rightOpposite
              rightOppositeSelected rightCertified rightCertifies =>
            exact .leaf (costStaticPlanCanonicalStop_of_reached leftRootPlan
              rightRootPlan
              (.collection leftChoice leftSelected leftChildren) _
              leftAdmission rightAdmission
              leftSkeletonContext rightSkeletonContext leftAbstractEq
              rightAbstractEq sourceTypeEq availableEq leftEmbedding rightEmbedding
              leftRoute rightRoute
              leftSizeLe rightSizeLe
              (Or.inr (by
                simp [CostStaticPlanStopEligible,
                  CostStaticRegionPlan.rootClass]))
              (.collection rawNe elementsAligned))
          | collection rightChoice rightSelected rightChildren =>
            by_cases sourceNe :
                collectionType ≠ declaration.parallelCollection
            · cases sourceTypeEq
              have elementTypeEq :=
                sourceElementType_eq_of_mem_costStaticCollectionTypingChoices
                  collectionDeterministic targetFree targetBound collectionType
                  leftElements rightElements
                  (mapTypeExpr (color.symbols source) leftSourceType) leftChoice
                  rightChoice leftSelected rightSelected
              have leftElementScope :
                  Pattern.isWellScopedListAt leftAvailable.length
                    leftElements = true := by
                simpa [WellSorted.ScopeSafeAt, Pattern.isWellScopedAt] using
                  leftAdmission.wellSorted.1.2.2.2
              have rightElementScope :
                  Pattern.isWellScopedListAt rightAvailable.length
                    rightElements = true := by
                simpa [WellSorted.ScopeSafeAt, Pattern.isWellScopedAt] using
                  rightAdmission.wellSorted.1.2.2.2
              have leftElementsTyped : WellSorted.ElementsHaveType
                  source.costWholeLanguage targetFree leftAvailable leftElements
                  (mapTypeExpr (color.symbols source)
                    leftChoice.sourceElementType) := by
                obtain ⟨sealed, targetBoundEq⟩ :=
                  leftAdmission.targetBound_split
                have typedAtTarget := WellSorted.checkElementsHaveType_sound
                  (checkElementsHaveType_of_mem_costStaticCollectionTypingChoices
                    leftSelected)
                rw [targetBoundEq] at typedAtTarget
                exact typedAtTarget.restrictOuterOfScoped leftElementScope
              have rightElementsTypedForChoice : WellSorted.ElementsHaveType
                  source.costWholeLanguage targetFree rightAvailable
                  rightElements (mapTypeExpr (color.symbols source)
                    rightChoice.sourceElementType) := by
                obtain ⟨sealed, targetBoundEq⟩ :=
                  rightAdmission.targetBound_split
                have typedAtTarget := WellSorted.checkElementsHaveType_sound
                  (checkElementsHaveType_of_mem_costStaticCollectionTypingChoices
                    rightSelected)
                rw [targetBoundEq] at typedAtTarget
                exact typedAtTarget.restrictOuterOfScoped rightElementScope
              have rightElementsTyped : WellSorted.ElementsHaveType
                  source.costWholeLanguage targetFree rightAvailable
                  rightElements (mapTypeExpr (color.symbols source)
                    leftChoice.sourceElementType) := by
                simpa [elementTypeEq] using rightElementsTypedForChoice
              have leftCanonicalElements :
                  Pattern.hasCanonicalBinderMetadataList leftElements = true := by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  leftAdmission.wellSorted.1.2.1
              have rightCanonicalElements :
                  Pattern.hasCanonicalBinderMetadataList rightElements = true := by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  rightAdmission.wellSorted.1.2.1
              have leftObjectElements :
                  WellSorted.isObjectPatternList leftElements = true := by
                simpa [WellSorted.isObjectPattern] using
                  leftAdmission.wellSorted.1.2.2.1
              have rightObjectElements :
                  WellSorted.isObjectPatternList rightElements = true := by
                simpa [WellSorted.isObjectPattern] using
                  rightAdmission.wellSorted.1.2.2.1
              have leftReflectiveElements : ∀ presentation ∈
                  source.costWholeReflectionProfile.presentations,
                  binderSafeListAt presentation.quoteConstructor
                    leftAvailable.length leftElements = true := by
                intro presentation membership
                simpa [binderSafeAt] using
                  leftAdmission.wellSorted.2 presentation membership
              have rightReflectiveElements : ∀ presentation ∈
                  source.costWholeReflectionProfile.presentations,
                  binderSafeListAt presentation.quoteConstructor
                    rightAvailable.length rightElements = true := by
                intro presentation membership
                simpa [binderSafeAt] using
                  rightAdmission.wellSorted.2 presentation membership
              have leftElementRoute :=
                costCanonicalTypeRoute_of_collectionChoice leftSelected
                  leftRoute
              have rightElementRoute :=
                (costCanonicalTypeRoute_of_collectionChoice rightSelected
                  rightRoute).map (fun route => route.castEndpoint (congrArg
                    (mapTypeExpr (color.symbols source)) elementTypeEq.symm))
              let rightChildren' :=
                rightChildren.castSourceElementType elementTypeEq
              have childrenAligned :=
                costStaticElementPlan_canonicalStopAligned
                  collectionDeterministic declaration rawDeclaration
                  leftRootPlan rightRootPlan
                  collectionType none [] [] leftChildren rightChildren'
                  leftElementsTyped rightElementsTyped leftCanonicalElements
                  rightCanonicalElements leftObjectElements
                  rightObjectElements leftReflectiveElements
                  rightReflectiveElements leftAdmission.targetBound_split
                  rightAdmission.targetBound_split
                  leftSkeletonContext rightSkeletonContext
                  (by simpa [CostStaticRegionPlan.abstractPattern] using
                    leftAbstractEq)
                  (by
                    rw [CostStaticElementPlan.abstractPatterns_castSourceElementType]
                    simpa [CostStaticRegionPlan.abstractPattern] using
                      rightAbstractEq)
                  (by
                    change CostStaticPlanEntryEmbedding source color targetFree
                      leftChildren.boundaryTable.entries
                      leftRootPlan.boundaryTable.entries at leftEmbedding
                    exact leftEmbedding)
                  (by
                    rw [CostStaticElementPlan.boundaryTable_entries_castSourceElementType]
                    change CostStaticPlanEntryEmbedding source color targetFree
                      rightChildren.boundaryTable.entries
                      rightRootPlan.boundaryTable.entries at rightEmbedding
                    exact rightEmbedding)
                  leftElementRoute rightElementRoute availableEq
                  (by simp at leftSizeLe ⊢; omega)
                  (by simp at rightSizeLe ⊢; omega)
                  elementsAligned
              simpa [rightChildren',
                CostStaticRegionPlan.abstractPattern,
                CostStaticElementPlan.abstractPatterns_castSourceElementType]
                using
                  (CanonicalStopAligned.collection sourceNe childrenAligned)
            · exact .leaf (costStaticPlanCanonicalStop_of_reached leftRootPlan
                rightRootPlan
                (.collection leftChoice leftSelected leftChildren)
                (.collection rightChoice rightSelected rightChildren)
                leftAdmission rightAdmission
                leftSkeletonContext rightSkeletonContext leftAbstractEq
                rightAbstractEq sourceTypeEq availableEq leftEmbedding
                rightEmbedding leftRoute rightRoute
                leftSizeLe rightSizeLe
                (Or.inr (by
                  simp at sourceNe
                  simpa [CostStaticPlanStopEligible,
                    CostStaticRegionPlan.rootClass] using
                    And.intro sourceNe sourceNe))
                (.collection rawNe elementsAligned))
    | @collectionRest collectionType rest leftElements rightElements
        elementsAligned =>
        exact (CostStaticRegionPlan.RawAdmission.not_collectionRest
          leftPlan leftAdmission).elim
  termination_by 3 * (sizeOf leftPattern + sizeOf rightPattern) + 2
  decreasing_by
    all_goals subst rightPattern
    all_goals subst leftPattern
    all_goals simp
    all_goals omega

  /-- Ordered-argument companion of plan canonical alignment. -/
  theorem costStaticArgumentPlan_canonicalStopAligned
      {source : CIGSLT} {color : CostStaticColor}
      (collectionDeterministic : CollectionChoiceDeterministic
        source.theory.presentation.presentation.language)
      (declaration : ReflectivePresentationDecl)
      (rawDeclaration : ReflectivePresentationDecl)
      {targetFree : WellSorted.FreeTypeContext}
      {rootSourceBound rootTargetBound : List TypeExpr}
      {rootThinning : CostStaticBinderThinning source color rootSourceBound
        rootTargetBound}
      {leftRootAvailable rightRootAvailable : List TypeExpr}
      {leftRootOuter rightRootOuter : OneHoleContext}
      {leftRoot rightRoot : Pattern} {rootSourceType : TypeExpr}
      (leftRootPlan : CostStaticRegionPlan source color targetFree
        rootSourceBound rootTargetBound rootThinning leftRootAvailable
        leftRootOuter leftRoot rootSourceType)
      (rightRootPlan : CostStaticRegionPlan source color targetFree
        rootSourceBound rootTargetBound rootThinning rightRootAvailable
        rightRootOuter rightRoot rootSourceType)
      {rawStop : Pattern → Pattern → Prop}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {leftAvailable rightAvailable : List TypeExpr}
      {leftOuter rightOuter : OneHoleContext} {wireName : String}
      {leftRawBefore rightRawBefore leftArguments rightArguments :
        List Pattern}
      {parameters : List TermParam}
      (sourceConstructor : String)
      (leftAbstractBefore rightAbstractBefore : List Pattern)
      (leftPlan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning leftAvailable leftOuter wireName leftRawBefore
        leftArguments parameters)
      (rightPlan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning rightAvailable rightOuter wireName rightRawBefore
        rightArguments parameters)
      (leftTyped : WellSorted.ArgumentsHaveTypes source.costWholeLanguage
        targetFree leftAvailable leftArguments
          (parameters.map (mapTermParam (color.symbols source))))
      (rightTyped : WellSorted.ArgumentsHaveTypes source.costWholeLanguage
        targetFree rightAvailable rightArguments
          (parameters.map (mapTermParam (color.symbols source))))
      (leftCanonical : Pattern.hasCanonicalBinderMetadataList leftArguments =
        true)
      (rightCanonical : Pattern.hasCanonicalBinderMetadataList rightArguments =
        true)
      (leftObjects : WellSorted.isObjectPatternList leftArguments = true)
      (rightObjects : WellSorted.isObjectPatternList rightArguments = true)
      (leftReflective : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor leftAvailable.length
          leftArguments = true)
      (rightReflective : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor rightAvailable.length
          rightArguments = true)
      (leftTargetBoundSplit : ∃ sealed,
        targetBound = leftAvailable ++ sealed)
      (rightTargetBoundSplit : ∃ sealed,
        targetBound = rightAvailable ++ sealed)
      (leftSkeletonContext rightSkeletonContext : OneHoleContext)
      (leftAbstractEq : leftRootPlan.abstractPattern =
        leftSkeletonContext.fill
          (.apply sourceConstructor
            (leftAbstractBefore ++ leftPlan.abstractPatterns)))
      (rightAbstractEq : rightRootPlan.abstractPattern =
        rightSkeletonContext.fill
          (.apply sourceConstructor
            (rightAbstractBefore ++ rightPlan.abstractPatterns)))
      (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
        leftPlan.boundaryTable.entries leftRootPlan.boundaryTable.entries)
      (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
        rightPlan.boundaryTable.entries rightRootPlan.boundaryTable.entries)
      (parameterRoute : ∀ {parameter : TermParam} {expected : TypeExpr},
        parameter ∈ parameters → parameterType? parameter = some expected →
          Nonempty (CostCanonicalTypeRoute source color
            (mapTypeExpr (color.symbols source) rootSourceType)
            (mapTypeExpr (color.symbols source) expected)))
      (availableEq : leftAvailable = rightAvailable)
      (leftArgumentsSizeLt : sizeOf leftArguments < sizeOf leftRoot)
      (rightArgumentsSizeLt : sizeOf rightArguments < sizeOf rightRoot)
      (rawAligned : CanonicalStopAlignedList
        rawDeclaration
        rawStop leftArguments rightArguments) :
      CanonicalStopAlignedList declaration
        (CostStaticPlanCanonicalStop leftRootPlan rightRootPlan declaration
          rawDeclaration
          rawStop)
        leftPlan.abstractPatterns rightPlan.abstractPatterns := by
    cases rawAligned with
    | nil =>
        cases leftPlan
        cases rightPlan
        cases leftTyped
        cases rightTyped
        exact .nil
    | cons headAligned tailAligned =>
        cases leftPlan with
        | cons leftRepresentation leftParameterType leftHead leftTail =>
          cases rightPlan with
          | cons rightRepresentation rightParameterType rightHead rightTail =>
            cases leftTyped with
            | @cons _ _ _ _ _ leftTargetExpected _ leftTargetParameterType
                leftHeadTyped leftTailTyped =>
              cases rightTyped with
              | @cons _ _ _ _ _ rightTargetExpected _ rightTargetParameterType
                  rightHeadTyped rightTailTyped =>
                simp [WellSorted.parameterType?_mapTermParam,
                  leftParameterType] at leftTargetParameterType
                simp [WellSorted.parameterType?_mapTermParam,
                  rightParameterType] at rightTargetParameterType
                subst leftTargetExpected
                subst rightTargetExpected
                have leftCanonicalParts := leftCanonical
                simp only [Pattern.hasCanonicalBinderMetadataList,
                  Bool.and_eq_true] at leftCanonicalParts
                have rightCanonicalParts := rightCanonical
                simp only [Pattern.hasCanonicalBinderMetadataList,
                  Bool.and_eq_true] at rightCanonicalParts
                have leftObjectParts := leftObjects
                simp only [WellSorted.isObjectPatternList,
                  Bool.and_eq_true] at leftObjectParts
                have rightObjectParts := rightObjects
                simp only [WellSorted.isObjectPatternList,
                  Bool.and_eq_true] at rightObjectParts
                have leftHeadAdmission : leftHead.RawAdmission :=
                  ⟨⟨⟨leftHeadTyped, leftCanonicalParts.1,
                    leftObjectParts.1, leftHeadTyped.isWellScopedAt⟩,
                    reflectiveScopeSafeAt_cons_head leftReflective⟩,
                    leftTargetBoundSplit⟩
                have rightHeadAdmission : rightHead.RawAdmission :=
                  ⟨⟨⟨rightHeadTyped, rightCanonicalParts.1,
                    rightObjectParts.1, rightHeadTyped.isWellScopedAt⟩,
                    reflectiveScopeSafeAt_cons_head rightReflective⟩,
                    rightTargetBoundSplit⟩
                have headSourceTypeEq :
                    _ = _ :=
                  Option.some.inj
                    (leftParameterType.symm.trans rightParameterType)
                have leftHeadRoute :=
                  parameterRoute List.mem_cons_self leftParameterType
                have rightHeadRoute :=
                  parameterRoute List.mem_cons_self rightParameterType
                let leftFrame : OneHoleContext :=
                  .apply sourceConstructor leftAbstractBefore .hole
                    leftTail.abstractPatterns
                let rightFrame : OneHoleContext :=
                  .apply sourceConstructor rightAbstractBefore .hole
                    rightTail.abstractPatterns
                have leftHeadEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      leftHead.boundaryTable.entries
                      leftRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.leftOfTableAppend
                    leftHead.boundaryTable leftTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append leftHead.boundaryTable
                      leftTail.boundaryTable).entries
                    leftRootPlan.boundaryTable.entries at leftEmbedding
                  exact leftEmbedding
                have rightHeadEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      rightHead.boundaryTable.entries
                      rightRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.leftOfTableAppend
                    rightHead.boundaryTable rightTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append rightHead.boundaryTable
                      rightTail.boundaryTable).entries
                    rightRootPlan.boundaryTable.entries at rightEmbedding
                  exact rightEmbedding
                have headResult := costStaticRegionPlan_canonicalStopAligned
                  collectionDeterministic declaration rawDeclaration
                  leftRootPlan rightRootPlan
                  leftHead rightHead leftHeadAdmission rightHeadAdmission
                  (leftSkeletonContext.comp leftFrame)
                  (rightSkeletonContext.comp rightFrame)
                  (by
                    rw [OneHoleContext.fill_comp]
                    simpa [leftFrame, OneHoleContext.fill,
                      CostStaticArgumentPlan.abstractPatterns,
                      List.append_assoc] using leftAbstractEq)
                  (by
                    rw [OneHoleContext.fill_comp]
                    simpa [rightFrame, OneHoleContext.fill,
                      CostStaticArgumentPlan.abstractPatterns,
                      List.append_assoc] using rightAbstractEq)
                  leftHeadEmbedding rightHeadEmbedding leftHeadRoute rightHeadRoute
                    headSourceTypeEq availableEq
                    (by simp at leftArgumentsSizeLt ⊢; omega)
                    (by simp at rightArgumentsSizeLt ⊢; omega)
                    headAligned
                have leftTailEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      leftTail.boundaryTable.entries
                      leftRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.rightOfTableAppend
                    leftHead.boundaryTable leftTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append leftHead.boundaryTable
                      leftTail.boundaryTable).entries
                    leftRootPlan.boundaryTable.entries at leftEmbedding
                  exact leftEmbedding
                have rightTailEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      rightTail.boundaryTable.entries
                      rightRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.rightOfTableAppend
                    rightHead.boundaryTable rightTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append rightHead.boundaryTable
                      rightTail.boundaryTable).entries
                    rightRootPlan.boundaryTable.entries at rightEmbedding
                  exact rightEmbedding
                exact .cons headResult
                  (costStaticArgumentPlan_canonicalStopAligned
                    collectionDeterministic declaration rawDeclaration
                    leftRootPlan rightRootPlan
                    sourceConstructor
                    (leftAbstractBefore ++ [leftHead.abstractPattern])
                    (rightAbstractBefore ++ [rightHead.abstractPattern])
                    leftTail rightTail leftTailTyped rightTailTyped
                    leftCanonicalParts.2 rightCanonicalParts.2
                    leftObjectParts.2 rightObjectParts.2
                    (binderSafeListAt_cons_tail leftReflective)
                    (binderSafeListAt_cons_tail rightReflective)
                    leftTargetBoundSplit rightTargetBoundSplit
                    leftSkeletonContext rightSkeletonContext
                    (by
                      simpa [CostStaticArgumentPlan.abstractPatterns,
                        List.append_assoc] using leftAbstractEq)
                    (by
                      simpa [CostStaticArgumentPlan.abstractPatterns,
                        List.append_assoc] using rightAbstractEq)
                    leftTailEmbedding rightTailEmbedding
                    (fun parameterMembership parameterTyped =>
                      parameterRoute
                        (List.mem_cons_of_mem _ parameterMembership)
                        parameterTyped)
                    availableEq
                    (by simp at leftArgumentsSizeLt ⊢; omega)
                    (by simp at rightArgumentsSizeLt ⊢; omega)
                    tailAligned)
  termination_by 3 * (sizeOf leftArguments + sizeOf rightArguments) + 1
  decreasing_by
    all_goals subst rightArguments
    all_goals subst leftArguments
    all_goals simp
    all_goals omega

  /-- Ordered arguments preserve canonical alignment while recording that
  every retained stop lies strictly below the enclosing application pair. -/
  theorem costStaticArgumentPlan_canonicalStopAlignedBelow
      {source : CIGSLT} {color : CostStaticColor}
      (collectionDeterministic : CollectionChoiceDeterministic
        source.theory.presentation.presentation.language)
      (declaration : ReflectivePresentationDecl)
      (rawDeclaration : ReflectivePresentationDecl)
      {targetFree : WellSorted.FreeTypeContext}
      {rootSourceBound rootTargetBound : List TypeExpr}
      {rootThinning : CostStaticBinderThinning source color rootSourceBound
        rootTargetBound}
      {leftRootAvailable rightRootAvailable : List TypeExpr}
      {leftRootOuter rightRootOuter : OneHoleContext}
      {leftRoot rightRoot : Pattern} {rootSourceType : TypeExpr}
      (leftRootPlan : CostStaticRegionPlan source color targetFree
        rootSourceBound rootTargetBound rootThinning leftRootAvailable
        leftRootOuter leftRoot rootSourceType)
      (rightRootPlan : CostStaticRegionPlan source color targetFree
        rootSourceBound rootTargetBound rootThinning rightRootAvailable
        rightRootOuter rightRoot rootSourceType)
      {rawStop : Pattern → Pattern → Prop}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {leftAvailable rightAvailable : List TypeExpr}
      {leftOuter rightOuter : OneHoleContext} {wireName : String}
      {leftRawBefore rightRawBefore leftArguments rightArguments :
        List Pattern}
      {parameters : List TermParam}
      (sourceConstructor : String)
      (leftAbstractBefore rightAbstractBefore : List Pattern)
      (leftPlan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning leftAvailable leftOuter wireName leftRawBefore
        leftArguments parameters)
      (rightPlan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning rightAvailable rightOuter wireName rightRawBefore
        rightArguments parameters)
      (leftTyped : WellSorted.ArgumentsHaveTypes source.costWholeLanguage
        targetFree leftAvailable leftArguments
          (parameters.map (mapTermParam (color.symbols source))))
      (rightTyped : WellSorted.ArgumentsHaveTypes source.costWholeLanguage
        targetFree rightAvailable rightArguments
          (parameters.map (mapTermParam (color.symbols source))))
      (leftCanonical : Pattern.hasCanonicalBinderMetadataList leftArguments =
        true)
      (rightCanonical : Pattern.hasCanonicalBinderMetadataList rightArguments =
        true)
      (leftObjects : WellSorted.isObjectPatternList leftArguments = true)
      (rightObjects : WellSorted.isObjectPatternList rightArguments = true)
      (leftReflective : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor leftAvailable.length
          leftArguments = true)
      (rightReflective : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor rightAvailable.length
          rightArguments = true)
      (leftTargetBoundSplit : ∃ sealed,
        targetBound = leftAvailable ++ sealed)
      (rightTargetBoundSplit : ∃ sealed,
        targetBound = rightAvailable ++ sealed)
      (leftSkeletonContext rightSkeletonContext : OneHoleContext)
      (leftAbstractEq : leftRootPlan.abstractPattern =
        leftSkeletonContext.fill
          (.apply sourceConstructor
            (leftAbstractBefore ++ leftPlan.abstractPatterns)))
      (rightAbstractEq : rightRootPlan.abstractPattern =
        rightSkeletonContext.fill
          (.apply sourceConstructor
            (rightAbstractBefore ++ rightPlan.abstractPatterns)))
      (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
        leftPlan.boundaryTable.entries leftRootPlan.boundaryTable.entries)
      (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
        rightPlan.boundaryTable.entries rightRootPlan.boundaryTable.entries)
      (parameterRoute : ∀ {parameter : TermParam} {expected : TypeExpr},
        parameter ∈ parameters → parameterType? parameter = some expected →
          Nonempty (CostCanonicalTypeRoute source color
            (mapTypeExpr (color.symbols source) rootSourceType)
            (mapTypeExpr (color.symbols source) expected)))
      (availableEq : leftAvailable = rightAvailable)
      (leftArgumentsSizeLt : sizeOf leftArguments < sizeOf leftRoot)
      (rightArgumentsSizeLt : sizeOf rightArguments < sizeOf rightRoot)
      (rawAligned : CanonicalStopAlignedList rawDeclaration rawStop
        leftArguments rightArguments) :
      CanonicalStopAlignedList declaration
        (CostStaticPlanCanonicalStopBelow leftRootPlan rightRootPlan declaration
          rawDeclaration rawStop (sizeOf leftRoot + sizeOf rightRoot))
        leftPlan.abstractPatterns rightPlan.abstractPatterns := by
    cases rawAligned with
    | nil =>
        cases leftPlan
        cases rightPlan
        cases leftTyped
        cases rightTyped
        exact .nil
    | cons headAligned tailAligned =>
        cases leftPlan with
        | cons leftRepresentation leftParameterType leftHead leftTail =>
          cases rightPlan with
          | cons rightRepresentation rightParameterType rightHead rightTail =>
            cases leftTyped with
            | @cons _ _ _ _ _ leftTargetExpected _ leftTargetParameterType
                leftHeadTyped leftTailTyped =>
              cases rightTyped with
              | @cons _ _ _ _ _ rightTargetExpected _ rightTargetParameterType
                  rightHeadTyped rightTailTyped =>
                simp [WellSorted.parameterType?_mapTermParam,
                  leftParameterType] at leftTargetParameterType
                simp [WellSorted.parameterType?_mapTermParam,
                  rightParameterType] at rightTargetParameterType
                subst leftTargetExpected
                subst rightTargetExpected
                have leftCanonicalParts := leftCanonical
                simp only [Pattern.hasCanonicalBinderMetadataList,
                  Bool.and_eq_true] at leftCanonicalParts
                have rightCanonicalParts := rightCanonical
                simp only [Pattern.hasCanonicalBinderMetadataList,
                  Bool.and_eq_true] at rightCanonicalParts
                have leftObjectParts := leftObjects
                simp only [WellSorted.isObjectPatternList,
                  Bool.and_eq_true] at leftObjectParts
                have rightObjectParts := rightObjects
                simp only [WellSorted.isObjectPatternList,
                  Bool.and_eq_true] at rightObjectParts
                have leftHeadAdmission : leftHead.RawAdmission :=
                  ⟨⟨⟨leftHeadTyped, leftCanonicalParts.1,
                    leftObjectParts.1, leftHeadTyped.isWellScopedAt⟩,
                    reflectiveScopeSafeAt_cons_head leftReflective⟩,
                    leftTargetBoundSplit⟩
                have rightHeadAdmission : rightHead.RawAdmission :=
                  ⟨⟨⟨rightHeadTyped, rightCanonicalParts.1,
                    rightObjectParts.1, rightHeadTyped.isWellScopedAt⟩,
                    reflectiveScopeSafeAt_cons_head rightReflective⟩,
                    rightTargetBoundSplit⟩
                have headSourceTypeEq : _ = _ :=
                  Option.some.inj
                    (leftParameterType.symm.trans rightParameterType)
                cases headSourceTypeEq
                have leftHeadRoute :=
                  parameterRoute List.mem_cons_self leftParameterType
                have rightHeadRoute :=
                  parameterRoute List.mem_cons_self rightParameterType
                let leftFrame : OneHoleContext :=
                  .apply sourceConstructor leftAbstractBefore .hole
                    leftTail.abstractPatterns
                let rightFrame : OneHoleContext :=
                  .apply sourceConstructor rightAbstractBefore .hole
                    rightTail.abstractPatterns
                have leftHeadRootEq : leftRootPlan.abstractPattern =
                    (leftSkeletonContext.comp leftFrame).fill
                      leftHead.abstractPattern := by
                  rw [OneHoleContext.fill_comp]
                  simpa [leftFrame, OneHoleContext.fill,
                    CostStaticArgumentPlan.abstractPatterns,
                    List.append_assoc] using leftAbstractEq
                have rightHeadRootEq : rightRootPlan.abstractPattern =
                    (rightSkeletonContext.comp rightFrame).fill
                      rightHead.abstractPattern := by
                  rw [OneHoleContext.fill_comp]
                  simpa [rightFrame, OneHoleContext.fill,
                    CostStaticArgumentPlan.abstractPatterns,
                    List.append_assoc] using rightAbstractEq
                have leftHeadEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      leftHead.boundaryTable.entries
                      leftRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.leftOfTableAppend
                    leftHead.boundaryTable leftTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append leftHead.boundaryTable
                      leftTail.boundaryTable).entries
                    leftRootPlan.boundaryTable.entries at leftEmbedding
                  exact leftEmbedding
                have rightHeadEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      rightHead.boundaryTable.entries
                      rightRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.leftOfTableAppend
                    rightHead.boundaryTable rightTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append rightHead.boundaryTable
                      rightTail.boundaryTable).entries
                    rightRootPlan.boundaryTable.entries at rightEmbedding
                  exact rightEmbedding
                have childResult := costStaticRegionPlan_canonicalStopAligned
                  collectionDeterministic declaration rawDeclaration
                  leftHead rightHead leftHead rightHead leftHeadAdmission
                  rightHeadAdmission .hole .hole rfl rfl
                  (CostStaticPlanEntryEmbedding.refl
                    leftHead.boundaryTable.entries)
                  (CostStaticPlanEntryEmbedding.refl
                    rightHead.boundaryTable.entries)
                  ⟨.refl⟩ ⟨.refl⟩ rfl availableEq le_rfl le_rfl
                  headAligned
                have headResult := canonicalStopAligned_map
                  (fun stopped => stopped.liftBelow leftRootPlan rightRootPlan
                    leftHead rightHead
                    (leftSkeletonContext.comp leftFrame)
                    (rightSkeletonContext.comp rightFrame)
                    leftHeadRootEq rightHeadRootEq leftHeadEmbedding
                    rightHeadEmbedding leftHeadRoute rightHeadRoute
                    (by simp at leftArgumentsSizeLt ⊢; omega)
                    (by simp at rightArgumentsSizeLt ⊢; omega) rfl)
                  childResult
                have leftTailEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      leftTail.boundaryTable.entries
                      leftRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.rightOfTableAppend
                    leftHead.boundaryTable leftTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append leftHead.boundaryTable
                      leftTail.boundaryTable).entries
                    leftRootPlan.boundaryTable.entries at leftEmbedding
                  exact leftEmbedding
                have rightTailEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      rightTail.boundaryTable.entries
                      rightRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.rightOfTableAppend
                    rightHead.boundaryTable rightTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append rightHead.boundaryTable
                      rightTail.boundaryTable).entries
                    rightRootPlan.boundaryTable.entries at rightEmbedding
                  exact rightEmbedding
                exact .cons headResult
                  (costStaticArgumentPlan_canonicalStopAlignedBelow
                    collectionDeterministic declaration rawDeclaration
                    leftRootPlan rightRootPlan sourceConstructor
                    (leftAbstractBefore ++ [leftHead.abstractPattern])
                    (rightAbstractBefore ++ [rightHead.abstractPattern])
                    leftTail rightTail leftTailTyped rightTailTyped
                    leftCanonicalParts.2 rightCanonicalParts.2
                    leftObjectParts.2 rightObjectParts.2
                    (binderSafeListAt_cons_tail leftReflective)
                    (binderSafeListAt_cons_tail rightReflective)
                    leftTargetBoundSplit rightTargetBoundSplit
                    leftSkeletonContext rightSkeletonContext
                    (by
                      simpa [CostStaticArgumentPlan.abstractPatterns,
                        List.append_assoc] using leftAbstractEq)
                    (by
                      simpa [CostStaticArgumentPlan.abstractPatterns,
                        List.append_assoc] using rightAbstractEq)
                    leftTailEmbedding rightTailEmbedding
                    (fun parameterMembership parameterTyped =>
                      parameterRoute
                        (List.mem_cons_of_mem _ parameterMembership)
                        parameterTyped)
                    availableEq
                    (by simp at leftArgumentsSizeLt ⊢; omega)
                    (by simp at rightArgumentsSizeLt ⊢; omega)
                    tailAligned)
  termination_by 3 * (sizeOf leftArguments + sizeOf rightArguments) + 1
  decreasing_by
    all_goals subst rightArguments
    all_goals subst leftArguments
    all_goals simp
    all_goals omega

  /-- Homogeneous-element companion of plan canonical alignment. -/
  private theorem costStaticElementPlan_canonicalStopAligned
      {source : CIGSLT} {color : CostStaticColor}
      (collectionDeterministic : CollectionChoiceDeterministic
        source.theory.presentation.presentation.language)
      (declaration : ReflectivePresentationDecl)
      (rawDeclaration : ReflectivePresentationDecl)
      {targetFree : WellSorted.FreeTypeContext}
      {rootSourceBound rootTargetBound : List TypeExpr}
      {rootThinning : CostStaticBinderThinning source color rootSourceBound
        rootTargetBound}
      {leftRootAvailable rightRootAvailable : List TypeExpr}
      {leftRootOuter rightRootOuter : OneHoleContext}
      {leftRoot rightRoot : Pattern} {rootSourceType : TypeExpr}
      (leftRootPlan : CostStaticRegionPlan source color targetFree
        rootSourceBound rootTargetBound rootThinning leftRootAvailable
        leftRootOuter leftRoot rootSourceType)
      (rightRootPlan : CostStaticRegionPlan source color targetFree
        rootSourceBound rootTargetBound rootThinning rightRootAvailable
        rightRootOuter rightRoot rootSourceType)
      {rawStop : Pattern → Pattern → Prop}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {leftAvailable rightAvailable : List TypeExpr}
      {leftOuter rightOuter : OneHoleContext} {collectionType : CollType}
      {rest : Option String}
      {leftRawBefore rightRawBefore leftElements rightElements : List Pattern}
      {sourceElementType : TypeExpr}
      (sourceCollectionType : CollType) (sourceRest : Option String)
      (leftAbstractBefore rightAbstractBefore : List Pattern)
      (leftPlan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning leftAvailable leftOuter collectionType
        leftRawBefore leftElements rest sourceElementType)
      (rightPlan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning rightAvailable rightOuter collectionType
        rightRawBefore rightElements rest sourceElementType)
      (leftTyped : WellSorted.ElementsHaveType source.costWholeLanguage
        targetFree leftAvailable leftElements
          (mapTypeExpr (color.symbols source) sourceElementType))
      (rightTyped : WellSorted.ElementsHaveType source.costWholeLanguage
        targetFree rightAvailable rightElements
          (mapTypeExpr (color.symbols source) sourceElementType))
      (leftCanonical : Pattern.hasCanonicalBinderMetadataList leftElements =
        true)
      (rightCanonical : Pattern.hasCanonicalBinderMetadataList rightElements =
        true)
      (leftObjects : WellSorted.isObjectPatternList leftElements = true)
      (rightObjects : WellSorted.isObjectPatternList rightElements = true)
      (leftReflective : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor leftAvailable.length
          leftElements = true)
      (rightReflective : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor rightAvailable.length
          rightElements = true)
      (leftTargetBoundSplit : ∃ sealed,
        targetBound = leftAvailable ++ sealed)
      (rightTargetBoundSplit : ∃ sealed,
        targetBound = rightAvailable ++ sealed)
      (leftSkeletonContext rightSkeletonContext : OneHoleContext)
      (leftAbstractEq : leftRootPlan.abstractPattern =
        leftSkeletonContext.fill
          (.collection sourceCollectionType
            (leftAbstractBefore ++ leftPlan.abstractPatterns) sourceRest))
      (rightAbstractEq : rightRootPlan.abstractPattern =
        rightSkeletonContext.fill
          (.collection sourceCollectionType
            (rightAbstractBefore ++ rightPlan.abstractPatterns) sourceRest))
      (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
        leftPlan.boundaryTable.entries leftRootPlan.boundaryTable.entries)
      (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
        rightPlan.boundaryTable.entries rightRootPlan.boundaryTable.entries)
      (leftElementRoute : Nonempty (CostCanonicalTypeRoute source color
        (mapTypeExpr (color.symbols source) rootSourceType)
        (mapTypeExpr (color.symbols source) sourceElementType)))
      (rightElementRoute : Nonempty (CostCanonicalTypeRoute source color
        (mapTypeExpr (color.symbols source) rootSourceType)
        (mapTypeExpr (color.symbols source) sourceElementType)))
      (availableEq : leftAvailable = rightAvailable)
      (leftElementsSizeLt : sizeOf leftElements < sizeOf leftRoot)
      (rightElementsSizeLt : sizeOf rightElements < sizeOf rightRoot)
      (rawAligned : CanonicalStopAlignedList
        rawDeclaration
        rawStop leftElements rightElements) :
      CanonicalStopAlignedList declaration
        (CostStaticPlanCanonicalStop leftRootPlan rightRootPlan declaration
          rawDeclaration
          rawStop)
        leftPlan.abstractPatterns rightPlan.abstractPatterns := by
    cases rawAligned with
    | nil =>
        cases leftPlan
        cases rightPlan
        cases leftTyped
        cases rightTyped
        exact .nil
    | cons headAligned tailAligned =>
        cases leftPlan with
        | cons leftHead leftTail =>
          cases rightPlan with
          | cons rightHead rightTail =>
            cases leftTyped with
            | cons leftHeadTyped leftTailTyped =>
              cases rightTyped with
              | cons rightHeadTyped rightTailTyped =>
                have leftCanonicalParts := leftCanonical
                simp only [Pattern.hasCanonicalBinderMetadataList,
                  Bool.and_eq_true] at leftCanonicalParts
                have rightCanonicalParts := rightCanonical
                simp only [Pattern.hasCanonicalBinderMetadataList,
                  Bool.and_eq_true] at rightCanonicalParts
                have leftObjectParts := leftObjects
                simp only [WellSorted.isObjectPatternList,
                  Bool.and_eq_true] at leftObjectParts
                have rightObjectParts := rightObjects
                simp only [WellSorted.isObjectPatternList,
                  Bool.and_eq_true] at rightObjectParts
                have leftHeadAdmission : leftHead.RawAdmission :=
                  ⟨⟨⟨leftHeadTyped, leftCanonicalParts.1,
                    leftObjectParts.1, leftHeadTyped.isWellScopedAt⟩,
                    reflectiveScopeSafeAt_cons_head leftReflective⟩,
                    leftTargetBoundSplit⟩
                have rightHeadAdmission : rightHead.RawAdmission :=
                  ⟨⟨⟨rightHeadTyped, rightCanonicalParts.1,
                    rightObjectParts.1, rightHeadTyped.isWellScopedAt⟩,
                    reflectiveScopeSafeAt_cons_head rightReflective⟩,
                    rightTargetBoundSplit⟩
                let leftFrame : OneHoleContext :=
                  .collection sourceCollectionType leftAbstractBefore .hole
                    leftTail.abstractPatterns sourceRest
                let rightFrame : OneHoleContext :=
                  .collection sourceCollectionType rightAbstractBefore .hole
                    rightTail.abstractPatterns sourceRest
                have leftHeadEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      leftHead.boundaryTable.entries
                      leftRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.leftOfTableAppend
                    leftHead.boundaryTable leftTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append leftHead.boundaryTable
                      leftTail.boundaryTable).entries
                    leftRootPlan.boundaryTable.entries at leftEmbedding
                  exact leftEmbedding
                have rightHeadEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      rightHead.boundaryTable.entries
                      rightRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.leftOfTableAppend
                    rightHead.boundaryTable rightTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append rightHead.boundaryTable
                      rightTail.boundaryTable).entries
                    rightRootPlan.boundaryTable.entries at rightEmbedding
                  exact rightEmbedding
                have headResult := costStaticRegionPlan_canonicalStopAligned
                  collectionDeterministic declaration rawDeclaration
                  leftRootPlan rightRootPlan
                  leftHead rightHead leftHeadAdmission rightHeadAdmission
                  (leftSkeletonContext.comp leftFrame)
                  (rightSkeletonContext.comp rightFrame)
                  (by
                    rw [OneHoleContext.fill_comp]
                    simpa [leftFrame, OneHoleContext.fill,
                      CostStaticElementPlan.abstractPatterns,
                      List.append_assoc] using leftAbstractEq)
                  (by
                    rw [OneHoleContext.fill_comp]
                    simpa [rightFrame, OneHoleContext.fill,
                      CostStaticElementPlan.abstractPatterns,
                      List.append_assoc] using rightAbstractEq)
                  leftHeadEmbedding rightHeadEmbedding leftElementRoute
                    rightElementRoute rfl availableEq
                    (by simp at leftElementsSizeLt ⊢; omega)
                    (by simp at rightElementsSizeLt ⊢; omega)
                    headAligned
                have leftTailEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      leftTail.boundaryTable.entries
                      leftRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.rightOfTableAppend
                    leftHead.boundaryTable leftTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append leftHead.boundaryTable
                      leftTail.boundaryTable).entries
                    leftRootPlan.boundaryTable.entries at leftEmbedding
                  exact leftEmbedding
                have rightTailEmbedding :
                    CostStaticPlanEntryEmbedding source color targetFree
                      rightTail.boundaryTable.entries
                      rightRootPlan.boundaryTable.entries := by
                  apply CostStaticPlanEntryEmbedding.rightOfTableAppend
                    rightHead.boundaryTable rightTail.boundaryTable
                  change CostStaticPlanEntryEmbedding source color targetFree
                    (TypedCostRegionBoundaryTable.append rightHead.boundaryTable
                      rightTail.boundaryTable).entries
                    rightRootPlan.boundaryTable.entries at rightEmbedding
                  exact rightEmbedding
                exact .cons headResult
                  (costStaticElementPlan_canonicalStopAligned
                    collectionDeterministic declaration rawDeclaration
                    leftRootPlan rightRootPlan
                    sourceCollectionType sourceRest
                    (leftAbstractBefore ++ [leftHead.abstractPattern])
                    (rightAbstractBefore ++ [rightHead.abstractPattern])
                    leftTail rightTail leftTailTyped rightTailTyped
                    leftCanonicalParts.2 rightCanonicalParts.2
                    leftObjectParts.2 rightObjectParts.2
                    (binderSafeListAt_cons_tail leftReflective)
                    (binderSafeListAt_cons_tail rightReflective)
                    leftTargetBoundSplit
                    rightTargetBoundSplit leftSkeletonContext
                    rightSkeletonContext
                    (by
                      simpa [CostStaticElementPlan.abstractPatterns,
                        List.append_assoc] using leftAbstractEq)
                    (by
                      simpa [CostStaticElementPlan.abstractPatterns,
                        List.append_assoc] using rightAbstractEq)
                    leftTailEmbedding rightTailEmbedding leftElementRoute
                    rightElementRoute availableEq
                    (by simp at leftElementsSizeLt ⊢; omega)
                    (by simp at rightElementsSizeLt ⊢; omega)
                    tailAligned)
  termination_by 3 * (sizeOf leftElements + sizeOf rightElements) + 1
  decreasing_by
    all_goals subst rightElements
    all_goals subst leftElements
    all_goals simp
    all_goals omega
end

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
/-- Homogeneous child descent whose every delegated stop is rebased into the
enclosing roots and certified strictly below their joint measure. -/
theorem costStaticElementPlan_canonicalStopAlignedBelow
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    {targetFree : WellSorted.FreeTypeContext}
    {rootSourceBound rootTargetBound : List TypeExpr}
    {rootThinning : CostStaticBinderThinning source color rootSourceBound
      rootTargetBound}
    {leftRootAvailable rightRootAvailable : List TypeExpr}
    {leftRootOuter rightRootOuter : OneHoleContext}
    {leftRoot rightRoot : Pattern} {rootSourceType : TypeExpr}
    (leftRootPlan : CostStaticRegionPlan source color targetFree
      rootSourceBound rootTargetBound rootThinning leftRootAvailable
      leftRootOuter leftRoot rootSourceType)
    (rightRootPlan : CostStaticRegionPlan source color targetFree
      rootSourceBound rootTargetBound rootThinning rightRootAvailable
      rightRootOuter rightRoot rootSourceType)
    {rawStop : Pattern → Pattern → Prop}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext} {collectionType : CollType}
    {rest : Option String}
    {leftRawBefore rightRawBefore leftElements rightElements : List Pattern}
    {sourceElementType : TypeExpr}
    (sourceCollectionType : CollType) (sourceRest : Option String)
    (leftAbstractBefore rightAbstractBefore : List Pattern)
    (leftPlan : CostStaticElementPlan source color targetFree sourceBound
      targetBound thinning leftAvailable leftOuter collectionType leftRawBefore
      leftElements rest sourceElementType)
    (rightPlan : CostStaticElementPlan source color targetFree sourceBound
      targetBound thinning rightAvailable rightOuter collectionType
      rightRawBefore rightElements rest sourceElementType)
    (leftTyped : WellSorted.ElementsHaveType source.costWholeLanguage
      targetFree leftAvailable leftElements
        (mapTypeExpr (color.symbols source) sourceElementType))
    (rightTyped : WellSorted.ElementsHaveType source.costWholeLanguage
      targetFree rightAvailable rightElements
        (mapTypeExpr (color.symbols source) sourceElementType))
    (leftCanonical : Pattern.hasCanonicalBinderMetadataList leftElements = true)
    (rightCanonical : Pattern.hasCanonicalBinderMetadataList rightElements = true)
    (leftObjects : WellSorted.isObjectPatternList leftElements = true)
    (rightObjects : WellSorted.isObjectPatternList rightElements = true)
    (leftReflective : ∀ presentation ∈
      source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor leftAvailable.length
        leftElements = true)
    (rightReflective : ∀ presentation ∈
      source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor rightAvailable.length
        rightElements = true)
    (leftTargetBoundSplit : ∃ sealed,
      targetBound = leftAvailable ++ sealed)
    (rightTargetBoundSplit : ∃ sealed,
      targetBound = rightAvailable ++ sealed)
    (leftSkeletonContext rightSkeletonContext : OneHoleContext)
    (leftAbstractEq : leftRootPlan.abstractPattern =
      leftSkeletonContext.fill
        (.collection sourceCollectionType
          (leftAbstractBefore ++ leftPlan.abstractPatterns) sourceRest))
    (rightAbstractEq : rightRootPlan.abstractPattern =
      rightSkeletonContext.fill
        (.collection sourceCollectionType
          (rightAbstractBefore ++ rightPlan.abstractPatterns) sourceRest))
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      leftPlan.boundaryTable.entries leftRootPlan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      rightPlan.boundaryTable.entries rightRootPlan.boundaryTable.entries)
    (leftElementRoute : Nonempty (CostCanonicalTypeRoute source color
      (mapTypeExpr (color.symbols source) rootSourceType)
      (mapTypeExpr (color.symbols source) sourceElementType)))
    (rightElementRoute : Nonempty (CostCanonicalTypeRoute source color
      (mapTypeExpr (color.symbols source) rootSourceType)
      (mapTypeExpr (color.symbols source) sourceElementType)))
    (availableEq : leftAvailable = rightAvailable)
    (leftElementsSizeLt : sizeOf leftElements < sizeOf leftRoot)
    (rightElementsSizeLt : sizeOf rightElements < sizeOf rightRoot)
    (rawAligned : CanonicalStopAlignedList rawDeclaration rawStop leftElements
      rightElements) :
    CanonicalStopAlignedList declaration
      (CostStaticPlanCanonicalStopBelow leftRootPlan rightRootPlan declaration
        rawDeclaration rawStop (sizeOf leftRoot + sizeOf rightRoot))
      leftPlan.abstractPatterns rightPlan.abstractPatterns := by
  cases rawAligned with
  | nil =>
      cases leftPlan
      cases rightPlan
      cases leftTyped
      cases rightTyped
      exact .nil
  | cons headAligned tailAligned =>
      cases leftPlan with
      | cons leftHead leftTail =>
        cases rightPlan with
        | cons rightHead rightTail =>
          cases leftTyped with
          | cons leftHeadTyped leftTailTyped =>
            cases rightTyped with
            | cons rightHeadTyped rightTailTyped =>
              have leftCanonicalParts := leftCanonical
              simp only [Pattern.hasCanonicalBinderMetadataList,
                Bool.and_eq_true] at leftCanonicalParts
              have rightCanonicalParts := rightCanonical
              simp only [Pattern.hasCanonicalBinderMetadataList,
                Bool.and_eq_true] at rightCanonicalParts
              have leftObjectParts := leftObjects
              simp only [WellSorted.isObjectPatternList,
                Bool.and_eq_true] at leftObjectParts
              have rightObjectParts := rightObjects
              simp only [WellSorted.isObjectPatternList,
                Bool.and_eq_true] at rightObjectParts
              have leftHeadAdmission : leftHead.RawAdmission :=
                ⟨⟨⟨leftHeadTyped, leftCanonicalParts.1, leftObjectParts.1,
                  leftHeadTyped.isWellScopedAt⟩,
                  reflectiveScopeSafeAt_cons_head leftReflective⟩,
                  leftTargetBoundSplit⟩
              have rightHeadAdmission : rightHead.RawAdmission :=
                ⟨⟨⟨rightHeadTyped, rightCanonicalParts.1, rightObjectParts.1,
                  rightHeadTyped.isWellScopedAt⟩,
                  reflectiveScopeSafeAt_cons_head rightReflective⟩,
                  rightTargetBoundSplit⟩
              let leftFrame : OneHoleContext :=
                .collection sourceCollectionType leftAbstractBefore .hole
                  leftTail.abstractPatterns sourceRest
              let rightFrame : OneHoleContext :=
                .collection sourceCollectionType rightAbstractBefore .hole
                  rightTail.abstractPatterns sourceRest
              have leftHeadRootEq : leftRootPlan.abstractPattern =
                  (leftSkeletonContext.comp leftFrame).fill
                    leftHead.abstractPattern := by
                rw [OneHoleContext.fill_comp]
                simpa [leftFrame, OneHoleContext.fill,
                  CostStaticElementPlan.abstractPatterns,
                  List.append_assoc] using leftAbstractEq
              have rightHeadRootEq : rightRootPlan.abstractPattern =
                  (rightSkeletonContext.comp rightFrame).fill
                    rightHead.abstractPattern := by
                rw [OneHoleContext.fill_comp]
                simpa [rightFrame, OneHoleContext.fill,
                  CostStaticElementPlan.abstractPatterns,
                  List.append_assoc] using rightAbstractEq
              have leftHeadEmbedding :
                  CostStaticPlanEntryEmbedding source color targetFree
                    leftHead.boundaryTable.entries
                    leftRootPlan.boundaryTable.entries := by
                apply CostStaticPlanEntryEmbedding.leftOfTableAppend
                  leftHead.boundaryTable leftTail.boundaryTable
                change CostStaticPlanEntryEmbedding source color targetFree
                  (TypedCostRegionBoundaryTable.append leftHead.boundaryTable
                    leftTail.boundaryTable).entries
                  leftRootPlan.boundaryTable.entries at leftEmbedding
                exact leftEmbedding
              have rightHeadEmbedding :
                  CostStaticPlanEntryEmbedding source color targetFree
                    rightHead.boundaryTable.entries
                    rightRootPlan.boundaryTable.entries := by
                apply CostStaticPlanEntryEmbedding.leftOfTableAppend
                  rightHead.boundaryTable rightTail.boundaryTable
                change CostStaticPlanEntryEmbedding source color targetFree
                  (TypedCostRegionBoundaryTable.append rightHead.boundaryTable
                    rightTail.boundaryTable).entries
                  rightRootPlan.boundaryTable.entries at rightEmbedding
                exact rightEmbedding
              have childResult := costStaticRegionPlan_canonicalStopAligned
                collectionDeterministic declaration rawDeclaration leftHead
                rightHead leftHead rightHead leftHeadAdmission rightHeadAdmission
                .hole .hole rfl rfl
                (CostStaticPlanEntryEmbedding.refl
                  leftHead.boundaryTable.entries)
                (CostStaticPlanEntryEmbedding.refl
                  rightHead.boundaryTable.entries)
                ⟨.refl⟩ ⟨.refl⟩ rfl availableEq le_rfl le_rfl headAligned
              have headResult := canonicalStopAligned_map
                (fun stopped => stopped.liftBelow leftRootPlan rightRootPlan
                  leftHead rightHead
                  (leftSkeletonContext.comp leftFrame)
                  (rightSkeletonContext.comp rightFrame)
                  leftHeadRootEq rightHeadRootEq leftHeadEmbedding
                  rightHeadEmbedding leftElementRoute rightElementRoute
                  (by simp at leftElementsSizeLt ⊢; omega)
                  (by simp at rightElementsSizeLt ⊢; omega) rfl)
                childResult
              have leftTailEmbedding :
                  CostStaticPlanEntryEmbedding source color targetFree
                    leftTail.boundaryTable.entries
                    leftRootPlan.boundaryTable.entries := by
                apply CostStaticPlanEntryEmbedding.rightOfTableAppend
                  leftHead.boundaryTable leftTail.boundaryTable
                change CostStaticPlanEntryEmbedding source color targetFree
                  (TypedCostRegionBoundaryTable.append leftHead.boundaryTable
                    leftTail.boundaryTable).entries
                  leftRootPlan.boundaryTable.entries at leftEmbedding
                exact leftEmbedding
              have rightTailEmbedding :
                  CostStaticPlanEntryEmbedding source color targetFree
                    rightTail.boundaryTable.entries
                    rightRootPlan.boundaryTable.entries := by
                apply CostStaticPlanEntryEmbedding.rightOfTableAppend
                  rightHead.boundaryTable rightTail.boundaryTable
                change CostStaticPlanEntryEmbedding source color targetFree
                  (TypedCostRegionBoundaryTable.append rightHead.boundaryTable
                    rightTail.boundaryTable).entries
                  rightRootPlan.boundaryTable.entries at rightEmbedding
                exact rightEmbedding
              exact .cons headResult
                (costStaticElementPlan_canonicalStopAlignedBelow
                  collectionDeterministic declaration rawDeclaration
                  leftRootPlan rightRootPlan sourceCollectionType sourceRest
                  (leftAbstractBefore ++ [leftHead.abstractPattern])
                  (rightAbstractBefore ++ [rightHead.abstractPattern])
                  leftTail rightTail leftTailTyped rightTailTyped
                  leftCanonicalParts.2 rightCanonicalParts.2
                  leftObjectParts.2 rightObjectParts.2
                  (binderSafeListAt_cons_tail leftReflective)
                  (binderSafeListAt_cons_tail rightReflective)
                  leftTargetBoundSplit rightTargetBoundSplit
                  leftSkeletonContext rightSkeletonContext
                  (by
                    simpa [CostStaticElementPlan.abstractPatterns,
                      List.append_assoc] using leftAbstractEq)
                  (by
                    simpa [CostStaticElementPlan.abstractPatterns,
                      List.append_assoc] using rightAbstractEq)
                  leftTailEmbedding rightTailEmbedding leftElementRoute
                  rightElementRoute availableEq
                  (by simp at leftElementsSizeLt ⊢; omega)
                  (by simp at rightElementsSizeLt ⊢; omega) tailAligned)
  termination_by 3 * (sizeOf leftElements + sizeOf rightElements) + 1
  decreasing_by
    all_goals subst rightElements
    all_goals subst leftElements
    all_goals simp
    all_goals omega

end Mettapedia.GSLT.LanguageDef
