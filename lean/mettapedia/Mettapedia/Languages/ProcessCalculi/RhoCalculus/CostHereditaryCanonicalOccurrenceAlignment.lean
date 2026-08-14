import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalOccurrenceAvailability

/-!
# Alignment certificate for canonical rho occurrences

The canonical occurrence inventory certificate retains exact positional
ancestry.  Alignment also needs the quote-local availability represented by
that position.  This module packages the existing rho availability dichotomy
with the ancestry token so downstream frame proofs do not reconstruct it from
an erased occurrence zipper.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- Exact source ancestry for a canonical occurrence, together with its
quote-local availability regime.

The first branch preserves the caller-relative availability.  The second
branch records a sealed source occurrence whose semantic atom is Name-sorted.
Both branches refer to the inherited positional source token. -/
structure RhoCanonicalInventoryOccurrenceAlignmentCertificate
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1))
    (ambient : List TypeExpr) : Type extends
      RhoCanonicalInventoryOccurrenceCertificate node environment
        targetOccurrence where
  availability_eq_or_sealed_name :
    rhoCanonicalOccurrenceAvailable ambient
        (planDecorationOccurrenceAt node inventory sourcePosition).context =
      rhoCanonicalOccurrenceAvailable ambient targetOccurrence.context ∨
    (rhoCanonicalOccurrenceAvailable ambient
          (planDecorationOccurrenceAt node inventory sourcePosition).context =
        [] ∧
      (environment.atomValue
        (environment.occurrenceSlot sourcePosition)).key.sourceType =
          TypeExpr.name)

/-- Package the existing positional ancestry and availability theorem into
the alignment certificate. -/
noncomputable def rhoCanonicalInventoryOccurrenceAlignmentCertificate
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1))
    (ambient : List TypeExpr) :
    RhoCanonicalInventoryOccurrenceAlignmentCertificate node environment
      targetOccurrence ambient := by
  let ancestry := rhoCanonicalInventoryOccurrenceCertificate node environment
    targetOccurrence
  exact { ancestry with
    availability_eq_or_sealed_name :=
      rhoCanonicalInventoryOccurrence_sourceAvailable_eq_targetAvailable_or_sourceName
        node environment targetOccurrence ambient }

/-- Two canonical occurrences with equal local availability induce exactly
three possible source regimes: equal availability, sealed on the left, or
sealed on the right.

This is the pairwise eliminator for the two independent ancestry
dichotomies.  The Name-sort side conditions remain stored in the
certificates for semantic leaf construction; no global support equality is
inferred here. -/
theorem RhoCanonicalInventoryOccurrenceAlignmentCertificate.sourceAvailabilities_eq_or_sealed
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    {leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory}
    {rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory}
    {leftTarget : CostStaticFVarOccurrence
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftNode leftEnvironment)
        rhoReflectivePresentation leftNode.targetBound.length 0
        (leftNode.reifiedSourceFrame leftEnvironment).1)}
    {rightTarget : CostStaticFVarOccurrence
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightNode rightEnvironment)
        rhoReflectivePresentation rightNode.targetBound.length 0
        (rightNode.reifiedSourceFrame rightEnvironment).1)}
    {ambient : List TypeExpr}
    (left : RhoCanonicalInventoryOccurrenceAlignmentCertificate leftNode
      leftEnvironment leftTarget ambient)
    (right : RhoCanonicalInventoryOccurrenceAlignmentCertificate rightNode
      rightEnvironment rightTarget ambient)
    (targetAvailableEq :
      rhoCanonicalOccurrenceAvailable ambient leftTarget.context =
        rhoCanonicalOccurrenceAvailable ambient rightTarget.context) :
    rhoCanonicalOccurrenceAvailable ambient
        (planDecorationOccurrenceAt leftNode leftInventory
          left.sourcePosition).context =
      rhoCanonicalOccurrenceAvailable ambient
        (planDecorationOccurrenceAt rightNode rightInventory
          right.sourcePosition).context ∨
    rhoCanonicalOccurrenceAvailable ambient
        (planDecorationOccurrenceAt leftNode leftInventory
          left.sourcePosition).context = [] ∨
    rhoCanonicalOccurrenceAvailable ambient
        (planDecorationOccurrenceAt rightNode rightInventory
          right.sourcePosition).context = [] := by
  rcases left.availability_eq_or_sealed_name with leftExposed | leftSealed
  · rcases right.availability_eq_or_sealed_name with
      rightExposed | rightSealed
    · exact Or.inl (leftExposed.trans
        (targetAvailableEq.trans rightExposed.symm))
    · exact Or.inr (Or.inr rightSealed.1)
  · exact Or.inr (Or.inl leftSealed.1)

private def alignmentAvailabilityCanary (source : CIGSLT)
    (available : List TypeExpr) : CostStaticPlanDecoration source :=
  .mk [] [] available .hole (.fvar "target") (.base "Canary") []
    (.fvar "source")

@[simp]
private theorem alignmentAvailabilityCanary_abstractPattern
    (source : CIGSLT) (available : List TypeExpr) :
    (alignmentAvailabilityCanary source available).abstractPattern =
      .fvar "source" := by
  simp [alignmentAvailabilityCanary,
    CostStaticPlanDecoration.abstractPattern,
    CostStaticPlanDecorationNode.abstractPattern]

/-! The availability field cannot be recovered from the raw occurrence
carrier.  This negative canary keeps the plan-indexed evidence requirement
visible at the alignment boundary. -/
theorem alignmentAvailability_not_recoverable_from_rawOccurrence
    (source : CIGSLT) (left right : List TypeExpr) (different : left ≠ right) :
    (alignmentAvailabilityCanary source left).abstractPattern =
        (alignmentAvailabilityCanary source right).abstractPattern ∧
      Nonempty (CostStaticPlanAbstractOccurrence source "source"
        (alignmentAvailabilityCanary source left) .hole left) ∧
      Nonempty (CostStaticPlanAbstractOccurrence source "source"
        (alignmentAvailabilityCanary source right) .hole right) ∧
      left ≠ right := by
  refine ⟨?_, ⟨.sourceFVar⟩, ⟨.sourceFVar⟩, different⟩
  simp

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
