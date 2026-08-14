import Mettapedia.GSLT.LanguageDef.CostCanonicalStopAlignment
import Mettapedia.GSLT.LanguageDef.CostCanonicalTypeRoute
import Mettapedia.GSLT.LanguageDef.CostStaticPlanSelection
import Mettapedia.GSLT.LanguageDef.CostWholeLanguageDeterminism
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion

/-!
# Canonical alignment of static-plan abstractions

Two static plans over canonically equal generated patterns need not retain
equal proof-relevant collection choices.  Their observable recursive indices
are nevertheless forced: applications have one authored constructor preimage,
and collection candidates at one expected type have one element type whenever
the source language has deterministic collection choices.

This file uses those projection laws to transport canonical structural descent
from generated patterns to their source-plan abstractions.  Every place where
the plan abstraction stops descending retains exact endpoint inventory views;
later semantic proofs can therefore recover boundary positions without
searching by name or assuming that duplicate entries are interchangeable.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open WellSorted

/-- Collection candidates selected at one target result type have the same
source element type, even when their concrete element lists differ.

The choices themselves are deliberately not equated: distinct bare rules may
erase to the same observable collection fibre. -/
theorem sourceElementType_eq_of_mem_costStaticCollectionTypingChoices
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic :
      CollectionChoiceDeterministic
        source.theory.presentation.presentation.language)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (collectionType : CollType)
    (leftElements rightElements : List Pattern) (expected : TypeExpr)
    (leftChoice rightChoice : CostCollectionTypingChoice)
    (leftMembership : leftChoice ∈
      costStaticCollectionTypingChoices source color targetFree targetBound
        collectionType leftElements expected)
    (rightMembership : rightChoice ∈
      costStaticCollectionTypingChoices source color targetFree targetBound
        collectionType rightElements expected) :
    leftChoice.sourceElementType = rightChoice.sourceElementType := by
  have resultTypeEquality :
      leftChoice.sourceResultType collectionType =
        rightChoice.sourceResultType collectionType := by
    apply mapTypeExpr_costStatic_injective source color
    exact
      (map_sourceResultType_eq_of_mem_costStaticCollectionTypingChoices
        source color targetFree targetBound collectionType leftElements
        expected leftChoice leftMembership).trans
      (map_sourceResultType_eq_of_mem_costStaticCollectionTypingChoices
        source color targetFree targetBound collectionType rightElements
        expected rightChoice rightMembership).symm
  rcases mem_costStaticCollectionTypingChoices_sound source color targetFree
      targetBound collectionType leftElements expected leftChoice
      leftMembership with leftDirect | leftBare
  · rcases leftDirect with
      ⟨leftElementType, leftChoiceEq, _expectedEq, _elementsChecked⟩
    subst leftChoice
    rcases mem_costStaticCollectionTypingChoices_sound source color targetFree
        targetBound collectionType rightElements expected rightChoice
        rightMembership with rightDirect | rightBare
    · rcases rightDirect with
        ⟨rightElementType, rightChoiceEq, _expectedEq, _elementsChecked⟩
      subst rightChoice
      exact TypeExpr.collection.inj resultTypeEquality |>.2
    · rcases rightBare with
        ⟨rightRule, rightElementType, rightChoiceEq, _membership, _wrapped,
          _expectedEq, _parameterName, _parameterShape, _elementsChecked⟩
      subst rightChoice
      cases resultTypeEquality
  · rcases leftBare with
      ⟨leftRule, leftElementType, leftChoiceEq, leftRuleMembership, _wrapped,
        _expectedEq, leftParameterName, leftParameterShape,
        _elementsChecked⟩
    subst leftChoice
    rcases mem_costStaticCollectionTypingChoices_sound source color targetFree
        targetBound collectionType rightElements expected rightChoice
        rightMembership with rightDirect | rightBare
    · rcases rightDirect with
        ⟨rightElementType, rightChoiceEq, _expectedEq, _elementsChecked⟩
      subst rightChoice
      cases resultTypeEquality
    · rcases rightBare with
        ⟨rightRule, rightElementType, rightChoiceEq, rightRuleMembership,
          _wrapped, _expectedEq, rightParameterName, rightParameterShape,
          _elementsChecked⟩
      subst rightChoice
      exact collectionDeterministic leftRuleMembership rightRuleMembership
        leftParameterShape rightParameterShape
        (TypeExpr.base.inj resultTypeEquality)

/-- Every selected collection choice carries the successful checker result
for exactly the source element type retained in that choice. -/
private theorem checkElementsHaveType_of_mem_costStaticCollectionTypingChoices
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {collectionType : CollType} {elements : List Pattern}
    {expected : TypeExpr} {choice : CostCollectionTypingChoice}
    (membership : choice ∈ costStaticCollectionTypingChoices source color
      targetFree targetBound collectionType elements expected) :
    WellSorted.checkElementsHaveType source.costWholeLanguage targetFree
      targetBound elements
        (mapTypeExpr (color.symbols source) choice.sourceElementType) = true := by
  rcases mem_costStaticCollectionTypingChoices_sound source color targetFree
      targetBound collectionType elements expected choice membership with
    direct | bare
  · rcases direct with
      ⟨sourceElementType, choiceEq, _expectedEq, checked⟩
    subst choice
    exact checked
  · rcases bare with
      ⟨rule, sourceElementType, choiceEq, _membership, _wrapped,
        _expectedEq, _parameterName, _parameterShape, checked⟩
    subst choice
    exact checked

/-! ## Provenance-bearing stops -/

/-- The root shape of a reached source plan, retaining only the distinction
needed to justify why canonical plan descent may stop. -/
inductive CostStaticPlanRootClass where
  | rigid
  | boundaryApplication
  | application (constructor : String)
  | boundaryCollection
  | collection (collectionType : CollType)
  deriving DecidableEq

/-- Root classification of a source plan.  This forgets proof terms and
payloads but retains every case in which the plan-alignment producer stops
before recursively pairing children. -/
def CostStaticRegionPlan.rootClass
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    CostStaticPlanRootClass :=
  match plan with
  | .boundaryApplication .. => .boundaryApplication
  | .application _ _ _ preimage _ _ =>
      .application preimage.sourceConstructor.1.label
  | .boundaryCollection .. => .boundaryCollection
  | .collection (collectionType := collectionType) .. =>
      .collection collectionType
  | _ => .rigid

/-- The semantic admission retained alongside a structural plan while
canonical alignment descends.  A plan by itself records the selected source
indices; it deliberately does not claim that an arbitrary inhabitant was
reached from an admitted target term.  The second field records the exact
reflective-availability prefix of the full target binder context. -/
structure CostStaticRegionPlan.RawAdmission
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) : Prop where
  wellSorted : ReflectiveWellSorted.OpenPatternWellSorted
    source.costWholeReflectionProfile source.costWholeLanguage targetFree
    sourceAvailable (mapTypeExpr (color.symbols source) sourceType) pattern
  targetBound_split : ∃ sealed, targetBound = sourceAvailable ++ sealed

namespace CostStaticRegionPlan.RawAdmission

/-- A retained admission always certifies an object pattern. -/
theorem object
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    {plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType}
    (admission : plan.RawAdmission) :
    WellSorted.isObjectPattern pattern = true :=
  admission.wellSorted.1.2.2.1

/-- Negative canary: a collection with an open tail may inhabit the raw plan
index, but it can never inhabit the semantic admission used by the producer. -/
theorem not_collectionRest
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {elements : List Pattern} {rest : String}
    {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer
      (.collection collectionType elements (some rest)) sourceType) :
    ¬ plan.RawAdmission := by
  intro admission
  have object := admission.object
  simp [WellSorted.isObjectPattern] at object

end CostStaticRegionPlan.RawAdmission

/-- Exact structural reasons for stopping source-plan descent independently
of a delegated raw stop.  Foreign applications are paired terminals; source
Quote applications stop before absorption; a foreign collection may face a
source collection; and two source bare parallels stop before sorting. -/
def CostStaticPlanStopEligible
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
    {leftPattern rightPattern : Pattern}
    {leftSourceType rightSourceType : TypeExpr}
    (declaration : ReflectivePresentationDecl)
    (leftPlan : CostStaticRegionPlan source color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPattern
      leftSourceType)
    (rightPlan : CostStaticRegionPlan source color targetFree rightSourceBound
      rightTargetBound rightThinning rightAvailable rightOuter rightPattern
      rightSourceType) : Prop :=
  match leftPlan.rootClass, rightPlan.rootClass with
  | .boundaryApplication, .boundaryApplication => True
  | .application leftConstructor, .application rightConstructor =>
      leftConstructor = declaration.quoteConstructor ∧
        rightConstructor = declaration.quoteConstructor
  | .boundaryCollection, .boundaryCollection => True
  | .boundaryCollection, .collection _ => True
  | .collection _, .boundaryCollection => True
  | .collection leftType, .collection rightType =>
      leftType = declaration.parallelCollection ∧
        rightType = declaration.parallelCollection
  | _, _ => False

/-- Positive structural boundary: two foreign applications are a legitimate
plan stop. -/
theorem costStaticPlanStopEligible_of_boundaryApplications
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
    {leftPattern rightPattern : Pattern}
    {leftSourceType rightSourceType : TypeExpr}
    (declaration : ReflectivePresentationDecl)
    (leftPlan : CostStaticRegionPlan source color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPattern
      leftSourceType)
    (rightPlan : CostStaticRegionPlan source color targetFree rightSourceBound
      rightTargetBound rightThinning rightAvailable rightOuter rightPattern
      rightSourceType)
    (leftClass : leftPlan.rootClass = .boundaryApplication)
    (rightClass : rightPlan.rootClass = .boundaryApplication) :
    CostStaticPlanStopEligible declaration leftPlan rightPlan := by
  simp [CostStaticPlanStopEligible, leftClass, rightClass]

/-- Negative structural boundary: rigid source leaves do not create an
independent plan stop.  They must remain in the rigid congruence or enter
through an explicit delegated raw stop. -/
theorem not_costStaticPlanStopEligible_of_rigid_left
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
    {leftPattern rightPattern : Pattern}
    {leftSourceType rightSourceType : TypeExpr}
    (declaration : ReflectivePresentationDecl)
    (leftPlan : CostStaticRegionPlan source color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPattern
      leftSourceType)
    (rightPlan : CostStaticRegionPlan source color targetFree rightSourceBound
      rightTargetBound rightThinning rightAvailable rightOuter rightPattern
      rightSourceType)
    (leftClass : leftPlan.rootClass = .rigid) :
    ¬ CostStaticPlanStopEligible declaration leftPlan rightPlan := by
  simp [CostStaticPlanStopEligible, leftClass]

/-- A stopped pair of abstract subpatterns, tied to exact reached subplans and
their replayable positions in the two root boundary inventories.

The raw alignment is retained at the selected payloads.  This is stronger
than merely recording that the abstract leaves are related: downstream
semantic arguments can reconstruct both plan contexts and distinguish equal
boundary values occurring at different finite positions. -/
def CostStaticPlanCanonicalStop
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
    (leftPlan : CostStaticRegionPlan source color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftRoot
      leftSourceType)
    (rightPlan : CostStaticRegionPlan source color targetFree rightSourceBound
      rightTargetBound rightThinning rightAvailable rightOuter rightRoot
      rightSourceType)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    (rawStop : Pattern → Pattern → Prop)
    (leftAbstract rightAbstract : Pattern) : Prop :=
  ∃ leftPayload rightPayload,
    ∃ leftReached : CostStaticPlanReached source color targetFree leftPayload
        leftPlan.abstractPattern,
    ∃ rightReached : CostStaticPlanReached source color targetFree rightPayload
        rightPlan.abstractPattern,
      leftReached.plan.RawAdmission ∧
      rightReached.plan.RawAdmission ∧
      leftReached.plan.abstractPattern = leftAbstract ∧
      rightReached.plan.abstractPattern = rightAbstract ∧
      leftReached.sourceType = rightReached.sourceType ∧
      leftReached.sourceAvailable = rightReached.sourceAvailable ∧
      Nonempty (CostStaticPlanEntryEmbedding source color targetFree
        leftReached.plan.boundaryTable.entries
        leftPlan.boundaryTable.entries) ∧
      Nonempty (CostStaticPlanEntryEmbedding source color targetFree
        rightReached.plan.boundaryTable.entries
        rightPlan.boundaryTable.entries) ∧
      Nonempty (CostCanonicalTypeRoute source color
        (mapTypeExpr (color.symbols source) leftSourceType)
        (mapTypeExpr (color.symbols source) leftReached.sourceType)) ∧
      Nonempty (CostCanonicalTypeRoute source color
        (mapTypeExpr (color.symbols source) rightSourceType)
        (mapTypeExpr (color.symbols source) rightReached.sourceType)) ∧
      (rawStop leftPayload rightPayload ∨
        CostStaticPlanStopEligible declaration leftReached.plan
          rightReached.plan) ∧
      CanonicalStopAligned rawDeclaration rawStop leftPayload rightPayload

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
      _leftEmbedding, _rightEmbedding, _leftRoute, _rightRoute, _stopReason,
      rawAligned⟩
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
    {leftPayloadSourceBound rightPayloadSourceBound
      leftPayloadTargetBound rightPayloadTargetBound : List TypeExpr}
    {leftPayloadThinning : CostStaticBinderThinning source color
      leftPayloadSourceBound leftPayloadTargetBound}
    {rightPayloadThinning : CostStaticBinderThinning source color
      rightPayloadSourceBound rightPayloadTargetBound}
    {leftPayloadAvailable rightPayloadAvailable : List TypeExpr}
    {leftPayloadOuter rightPayloadOuter : OneHoleContext}
    (leftPayloadPlan : CostStaticRegionPlan source color targetFree
      leftPayloadSourceBound leftPayloadTargetBound leftPayloadThinning
      leftPayloadAvailable leftPayloadOuter leftPayload leftPayloadType)
    (rightPayloadPlan : CostStaticRegionPlan source color targetFree
      rightPayloadSourceBound rightPayloadTargetBound rightPayloadThinning
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
    { sourceBound := leftPayloadSourceBound
      targetBound := leftPayloadTargetBound
      thinning := leftPayloadThinning
      sourceAvailable := leftPayloadAvailable
      outer := leftPayloadOuter
      sourceType := leftPayloadType
      plan := leftPayloadPlan
      skeletonContext := leftSkeletonContext
      abstract_eq := leftAbstractEq }
  let rightReached : CostStaticPlanReached source color targetFree rightPayload
      rightRootPlan.abstractPattern :=
    { sourceBound := rightPayloadSourceBound
      targetBound := rightPayloadTargetBound
      thinning := rightPayloadThinning
      sourceAvailable := rightPayloadAvailable
      outer := rightPayloadOuter
      sourceType := rightPayloadType
      plan := rightPayloadPlan
      skeletonContext := rightSkeletonContext
      abstract_eq := rightAbstractEq }
  refine ⟨leftPayload, rightPayload, leftReached, rightReached, ?_, ?_, rfl,
    rfl, ?_, ?_, ?_, ?_, leftRoute, rightRoute, ?_, rawAligned⟩
  · simpa [leftReached] using leftAdmission
  · simpa [rightReached] using rightAdmission
  · simpa [leftReached, rightReached] using payloadTypeEq
  · simpa [leftReached, rightReached] using payloadAvailableEq
  · exact ⟨leftEmbedding⟩
  · exact ⟨rightEmbedding⟩
  · simpa [leftReached, rightReached] using stopReason

/-- Reindex only the homogeneous element fibre of an element plan.  No raw
element, occurrence position, or boundary table is changed. -/
private def CostStaticElementPlan.castSourceElementType
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
private theorem CostStaticElementPlan.abstractPatterns_castSourceElementType
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
private theorem CostStaticElementPlan.boundaryTable_entries_castSourceElementType
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
private theorem costCanonicalTypeRoute_of_collectionChoice
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
  private def costStaticRegionPlan_canonicalStopAligned
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
                    rfl argumentsAligned
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
    all_goals subst_vars
    all_goals simp
    all_goals omega

  /-- Ordered-argument companion of plan canonical alignment. -/
  private def costStaticArgumentPlan_canonicalStopAligned
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
                    headSourceTypeEq availableEq headAligned
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
                    availableEq tailAligned)
  termination_by 3 * (sizeOf leftArguments + sizeOf rightArguments) + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp
    all_goals omega

  /-- Homogeneous-element companion of plan canonical alignment. -/
  private def costStaticElementPlan_canonicalStopAligned
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
                    rightElementRoute rfl availableEq headAligned
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
                    rightElementRoute availableEq tailAligned)
  termination_by 3 * (sizeOf leftElements + sizeOf rightElements) + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp
    all_goals omega
end

/-- Transport any stopped raw alignment through two static plans.

The raw and source declarations are intentionally independent.  A root that
is rigid for the raw declaration but reflective for the authored source
declaration becomes a provenance-bearing stop rather than being traversed.
This is the interface used when a provider canonicalizes a same-colour pair
with the other generated Cost declaration. -/
theorem CostStaticRegionPlan.canonicalStopAligned_of_rawAlignment
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPattern rightPattern : Pattern} {sourceType : TypeExpr}
    (leftPlan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning leftAvailable leftOuter leftPattern sourceType)
    (rightPlan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning rightAvailable rightOuter rightPattern sourceType)
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (availableEq : leftAvailable = rightAvailable)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPattern
      rightPattern) :
    CanonicalStopAligned declaration
      (CostStaticPlanCanonicalStop leftPlan rightPlan declaration
        rawDeclaration rawStop)
      leftPlan.abstractPattern rightPlan.abstractPattern := by
  apply costStaticRegionPlan_canonicalStopAligned collectionDeterministic
    declaration rawDeclaration leftPlan rightPlan leftPlan rightPlan
    leftAdmission rightAdmission .hole .hole
  · rfl
  · rfl
  · exact CostStaticPlanEntryEmbedding.refl leftPlan.boundaryTable.entries
  · exact CostStaticPlanEntryEmbedding.refl rightPlan.boundaryTable.entries
  · exact ⟨.refl⟩
  · exact ⟨.refl⟩
  · rfl
  · exact availableEq
  · exact rawAligned

/-- Canonically equal generated endpoints induce a rigid alignment of their
source-plan abstractions.  The descent stops only at raw roots where
reflective canonicalization may collapse; every such stop retains exact
reached-plan and root-table provenance on both sides. -/
theorem CostStaticRegionPlan.canonicalStopAligned_of_canonicalize_eq
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration : ReflectivePresentationDecl)
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPattern rightPattern : Pattern} {sourceType : TypeExpr}
    (leftPlan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning leftAvailable leftOuter leftPattern sourceType)
    (rightPlan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning rightAvailable rightOuter rightPattern sourceType)
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (availableEq : leftAvailable = rightAvailable)
    (canonicalEq : canonicalize
        (costStaticReflectivePresentationDecl source color declaration)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl source color declaration)
        rightPattern) :
    CanonicalStopAligned declaration
      (CostStaticPlanCanonicalStop leftPlan rightPlan
        declaration
        (costStaticReflectivePresentationDecl source color declaration)
        (fun candidateLeft candidateRight =>
          (CollapsingRoot
              (costStaticReflectivePresentationDecl source color declaration)
              candidateLeft ∨
            CollapsingRoot
              (costStaticReflectivePresentationDecl source color declaration)
              candidateRight) ∧
          canonicalize
              (costStaticReflectivePresentationDecl source color declaration)
              candidateLeft =
            canonicalize
              (costStaticReflectivePresentationDecl source color declaration)
              candidateRight))
      leftPlan.abstractPattern rightPlan.abstractPattern := by
  exact leftPlan.canonicalStopAligned_of_rawAlignment
    collectionDeterministic declaration
    (costStaticReflectivePresentationDecl source color declaration) rightPlan
    leftAdmission rightAdmission availableEq
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalStopAligned_of_canonicalize_eq
      (costStaticReflectivePresentationDecl source color declaration)
      canonicalEq)

/-- A plan stop cannot be fabricated when the raw alignment relation rejects
every possible reached payload pair. -/
theorem not_costStaticPlanCanonicalStop_of_no_raw_alignment
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPattern rightPattern : Pattern} {sourceType : TypeExpr}
    (leftPlan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning leftAvailable leftOuter leftPattern sourceType)
    (rightPlan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning rightAvailable rightOuter rightPattern sourceType)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    (rawStop : Pattern → Pattern → Prop)
    (reject : ∀ leftPayload rightPayload,
      ¬ CanonicalStopAligned rawDeclaration rawStop leftPayload rightPayload)
    (leftAbstract rightAbstract : Pattern) :
    ¬ CostStaticPlanCanonicalStop leftPlan rightPlan declaration
      rawDeclaration rawStop leftAbstract rightAbstract := by
  rintro ⟨leftPayload, rightPayload, _leftReached, _rightReached,
    _leftAdmission, _rightAdmission,
    _leftAbstractEq, _rightAbstractEq, _sourceTypeEq, _sourceAvailableEq,
    _leftEmbedding, _rightEmbedding, _leftRoute, _rightRoute, _stopReason,
    rawAligned⟩
  exact reject leftPayload rightPayload rawAligned

end Mettapedia.GSLT.LanguageDef
