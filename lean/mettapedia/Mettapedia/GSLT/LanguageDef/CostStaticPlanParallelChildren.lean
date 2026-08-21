import Mettapedia.GSLT.LanguageDef.CostStaticPlanLockstep

/-!
# Strict child alignment beneath a bare-parallel stop

The parallel shell may reorder occurrences, so the ordinary plan-alignment
interface stops there.  This module exposes the child alignment underneath
it, with every stop certified strictly below the parent measure, which is
what licenses well-founded recursion in the restoration layer.
-/
namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open WellSorted
/-- Expose the recursively aligned abstract elements retained beneath a pair
of reached bare-parallel plans.  The ordinary plan-alignment interface stops
at the parallel shell because that shell may reorder occurrences; the
proof-relevant restoration layer instead needs the child alignment before it
rebuilds the shell with an explicit permutation witness. -/
theorem CostStaticRegionPlan.parallelChildrenCanonicalStopAligned_of_rawAlignment
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftElements rightElements : List Pattern} {sourceType : TypeExpr}
    (leftPlan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning leftAvailable leftOuter
      (.collection declaration.parallelCollection leftElements none)
      sourceType)
    (rightPlan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning rightAvailable rightOuter
      (.collection declaration.parallelCollection rightElements none)
      sourceType)
    (leftClass : leftPlan.rootClass =
      .collection declaration.parallelCollection)
    (rightClass : rightPlan.rootClass =
      .collection declaration.parallelCollection)
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (availableEq : leftAvailable = rightAvailable)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop
      (.collection declaration.parallelCollection leftElements none)
      (.collection declaration.parallelCollection rightElements none))
    (notDelegated : ¬ ∃ stopped,
      rawAligned = CanonicalStopAligned.leaf stopped) :
    ∃ leftAbstractElements rightAbstractElements,
      leftPlan.abstractPattern =
          .collection declaration.parallelCollection leftAbstractElements none ∧
        rightPlan.abstractPattern =
          .collection declaration.parallelCollection rightAbstractElements none ∧
        CanonicalStopAlignedList declaration
          (CostStaticPlanCanonicalStopBelow leftPlan rightPlan declaration
            rawDeclaration rawStop
            (sizeOf (Pattern.collection declaration.parallelCollection
                leftElements none) +
              sizeOf (Pattern.collection declaration.parallelCollection
                rightElements none)))
          leftAbstractElements rightAbstractElements := by
  cases rawAligned with
  | leaf given => exact (notDelegated ⟨given, rfl⟩).elim
  | collection rawNe elementsAligned =>
      cases leftPlan with
      | boundaryCollection leftRejected leftOpposite leftOppositeSelected
          leftCertified leftCertifies =>
          simp [CostStaticRegionPlan.rootClass] at leftClass
      | collection leftChoice leftSelected leftChildren =>
          cases rightPlan with
          | boundaryCollection rightRejected rightOpposite
              rightOppositeSelected rightCertified rightCertifies =>
              simp [CostStaticRegionPlan.rootClass] at rightClass
          | collection rightChoice rightSelected rightChildren =>
              have elementTypeEq :=
                sourceElementType_eq_of_mem_costStaticCollectionTypingChoices
                  collectionDeterministic targetFree targetBound
                  declaration.parallelCollection leftElements rightElements
                  (mapTypeExpr (color.symbols source) sourceType) leftChoice
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
                  source.costWholeLanguage targetFree leftAvailable
                  leftElements
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
                  rightElements
                  (mapTypeExpr (color.symbols source)
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
                  rightElements
                  (mapTypeExpr (color.symbols source)
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
              let rightChildren' :=
                rightChildren.castSourceElementType elementTypeEq
              have leftElementRoute :=
                costCanonicalTypeRoute_of_collectionChoice leftSelected
                  (⟨CostCanonicalTypeRoute.refl⟩ : Nonempty
                    (CostCanonicalTypeRoute source color
                      (mapTypeExpr (color.symbols source) sourceType)
                      (mapTypeExpr (color.symbols source) sourceType)))
              have rightElementRoute :=
                (costCanonicalTypeRoute_of_collectionChoice rightSelected
                  (⟨CostCanonicalTypeRoute.refl⟩ : Nonempty
                    (CostCanonicalTypeRoute source color
                      (mapTypeExpr (color.symbols source) sourceType)
                      (mapTypeExpr (color.symbols source) sourceType)))).map
                    (fun route => route.castEndpoint (congrArg
                      (mapTypeExpr (color.symbols source))
                        elementTypeEq.symm))
              have childrenAligned :=
                costStaticElementPlan_canonicalStopAlignedBelow
                  collectionDeterministic declaration rawDeclaration
                  (.collection leftChoice leftSelected leftChildren)
                  (.collection rightChoice rightSelected rightChildren)
                  declaration.parallelCollection none [] [] leftChildren
                  rightChildren' leftElementsTyped rightElementsTyped
                  leftCanonicalElements rightCanonicalElements
                  leftObjectElements rightObjectElements
                  leftReflectiveElements rightReflectiveElements
                  leftAdmission.targetBound_split
                  rightAdmission.targetBound_split .hole .hole rfl
                  (by
                    rw [CostStaticElementPlan.abstractPatterns_castSourceElementType]
                    rfl)
                  (CostStaticPlanEntryEmbedding.refl
                    leftChildren.boundaryTable.entries)
                  (by
                    rw [CostStaticElementPlan.boundaryTable_entries_castSourceElementType]
                    exact CostStaticPlanEntryEmbedding.refl
                      rightChildren.boundaryTable.entries)
                  leftElementRoute rightElementRoute availableEq
                  (by simp_wf; omega)
                  (by simp_wf; omega)
                  elementsAligned
              refine ⟨leftChildren.abstractPatterns,
                rightChildren.abstractPatterns, rfl, rfl, ?_⟩
              simpa [rightChildren',
                CostStaticElementPlan.abstractPatterns_castSourceElementType]
                using childrenAligned

end Mettapedia.GSLT.LanguageDef
