import Mettapedia.GSLT.LanguageDef.CostStaticPlanLockstep

/-!
# Canonical-alignment producers

The public entry points: stopped alignment from a raw alignment, its
same-declaration specialization from canonical equality, and the negative
theorem refusing a fabricated stop.
-/
namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open WellSorted
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
  · exact le_rfl
  · exact le_rfl
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
    _sourceBoundEq, _targetBoundEq, _thinningEq,
    _leftEmbedding, _rightEmbedding, _leftRoute, _rightRoute, _stopReason,
    _leftSizeLe, _rightSizeLe, rawAligned⟩
  exact reject leftPayload rightPayload rawAligned

end Mettapedia.GSLT.LanguageDef
