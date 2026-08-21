import Mettapedia.GSLT.LanguageDef.CostCanonicalStopAlignment
import Mettapedia.GSLT.LanguageDef.CostCanonicalTypeRoute
import Mettapedia.GSLT.LanguageDef.CostStaticPlanBoundaryFibers
import Mettapedia.GSLT.LanguageDef.CostStaticPlanSelection
import Mettapedia.GSLT.LanguageDef.CostWholeLanguageDeterminism
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion

/-!
# Static-plan stop carriers

Root classification, raw admission, stop eligibility, and the three stop
carriers (`CostStaticPlanCanonicalStopAtPayload`, `...Stop`, `...StopBelow`)
with the forgetting theorem between the last two.  These are the exact
provenance records every later canonical-alignment proof transports; the
transport itself lives downstream in `CostStaticPlanLockstep`.
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
theorem checkElementsHaveType_of_mem_costStaticCollectionTypingChoices
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

namespace CostStaticPlanReached

/-- Rebuild an admitted reached payload at its visible root fibre and relate
that executable plan to the contextual plan by a sealed availability suffix.
The compiler receipt is retained: later consumers may construct the exact
root static node without rerunning or guessing the authoritative plan. -/
theorem exists_rootPlanSealedAlignment
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (unique : CostStaticCollectionGloballyUnambiguous source)
    (reached : CostStaticPlanReached source color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission) :
    ∃ (sealed : List TypeExpr)
        (rootPlan : CostStaticRegionPlan source color targetFree
          (CostStaticBinderThinning.sourceContextOfTarget source color
            reached.sourceAvailable)
          reached.sourceAvailable
          (CostStaticBinderThinning.ofTargetThinning source color
            reached.sourceAvailable)
          reached.sourceAvailable .hole payload reached.sourceType),
      reached.targetBound = reached.sourceAvailable ++ sealed ∧
        buildCostStaticRegionPlan? source color targetFree
            (CostStaticBinderThinning.sourceContextOfTarget source color
              reached.sourceAvailable)
            reached.sourceAvailable
            (CostStaticBinderThinning.ofTargetThinning source color
              reached.sourceAvailable)
            reached.sourceAvailable .hole payload reached.sourceType =
          some rootPlan ∧
        CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix sealed .sealed
          rootPlan (reached.plan.recontextualize .hole) := by
  obtain ⟨sealed, split⟩ := admission.targetBound_split
  obtain ⟨rootPlan, rootBuilt⟩ :=
    exists_buildCostStaticRegionPlan?_root_of_wellSorted
      reached.sourceAvailable payload reached.sourceType admission.wellSorted
  refine ⟨sealed, rootPlan, split, rootBuilt, ?_⟩
  apply CostStaticRegionPlan.boundaryFibersAvailabilitySuffix_of_scoped
    unique (regime := .sealed) (ambient := sealed)
      (smallTargetBound := reached.sourceAvailable)
  · rfl
  · exact split
  · rfl
  · exact admission.object
  · exact admission.wellSorted.1.1.isWellScopedAt

end CostStaticPlanReached

namespace CostStaticRegionNode

/-- The certified static-node producer retains exactly the semantic admission
needed by canonical plan descent.  Reflective well-sortedness comes from
restoring the node's original boundary values through its support-safe source
skeleton; it is not reconstructed from ordinary target typing. -/
theorem planRawAdmission
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    node.plan.RawAdmission := by
  refine ⟨?_, ⟨[], by simp⟩⟩
  change ReflectiveWellSorted.OpenPatternWellSorted
    source.costWholeReflectionProfile source.costWholeLanguage targetFree
      node.targetBound
      (.base (color.mapLangSort source node.sourceSort).1) node.term.1
  exact node.termReflective.2

end CostStaticRegionNode

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

/-- The payload-indexed evidence carried by one canonical plan stop.  Factoring
the payloads from the outer existential lets specialized recursive consumers
retain an additional well-founded measure without duplicating the dependent
provenance telescope. -/
def CostStaticPlanCanonicalStopAtPayload
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
    (leftPayload rightPayload leftAbstract rightAbstract : Pattern) : Prop :=
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
    leftReached.sourceBound = rightReached.sourceBound ∧
    leftReached.targetBound = rightReached.targetBound ∧
    HEq leftReached.thinning rightReached.thinning ∧
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
    sizeOf leftPayload ≤ sizeOf leftRoot ∧
    sizeOf rightPayload ≤ sizeOf rightRoot ∧
    CanonicalStopAligned rawDeclaration rawStop leftPayload rightPayload

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
    CostStaticPlanCanonicalStopAtPayload leftPlan rightPlan declaration
      rawDeclaration rawStop leftPayload rightPayload leftAbstract rightAbstract

/-- A canonical plan stop known to lie strictly below a supplied recursive
measure.  It carries exactly the ordinary stop evidence plus the strict pair
bound produced by structural child descent. -/
def CostStaticPlanCanonicalStopBelow
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
    (rawStop : Pattern → Pattern → Prop) (parentMeasure : Nat)
    (leftAbstract rightAbstract : Pattern) : Prop :=
  ∃ leftPayload rightPayload,
    CostStaticPlanCanonicalStopAtPayload leftPlan rightPlan declaration
        rawDeclaration rawStop leftPayload rightPayload leftAbstract
          rightAbstract ∧
      sizeOf leftPayload + sizeOf rightPayload < parentMeasure

/-- Forgetting the strict recursive certificate recovers an ordinary plan
stop without changing any proof-relevant provenance. -/
theorem CostStaticPlanCanonicalStopBelow.toCanonicalStop
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
    {rawStop : Pattern → Pattern → Prop} {parentMeasure : Nat}
    {leftAbstract rightAbstract : Pattern}
    (stopped : CostStaticPlanCanonicalStopBelow leftPlan rightPlan declaration
      rawDeclaration rawStop parentMeasure leftAbstract rightAbstract) :
    CostStaticPlanCanonicalStop leftPlan rightPlan declaration rawDeclaration
      rawStop leftAbstract rightAbstract := by
  rcases stopped with ⟨leftPayload, rightPayload, evidence, _smaller⟩
  exact ⟨leftPayload, rightPayload, evidence⟩
end Mettapedia.GSLT.LanguageDef
