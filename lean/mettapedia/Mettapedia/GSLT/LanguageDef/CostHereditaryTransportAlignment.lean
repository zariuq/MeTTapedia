import Mettapedia.GSLT.LanguageDef.CostHereditaryTransportAtoms

/-!
# Hereditary alignment of structural Cost transport

The proof-relevant structural transport already handles every neutral frame,
binder, substitution frame, collection spine, and nonlinear boundary
pullback.  Exact hereditary normalization therefore has one genuinely local
obligation: close a transported pair of static roots after their recursively
selected children have been aligned.

This file isolates that obligation and proves the complete mutual structural
assembly.  It does not assert a static closure for any language; a concrete
language must construct the root bridge from its authored generator and
restoration semantics.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- Local exactness obligation for one transported static root.

The premise retains the actual plan edge and recursive child transports.
Recursive exactness is supplied as `Nonempty` alignment evidence because the
transport relation is proposition-valued; no proof-relevant alignment is
chosen or cached by the structural carrier itself. -/
def CostStaticTransportNormalizationClosed
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    (staticLift : CostStaticPlanLift source) : Prop :=
  ∀ {targetFree : FreeTypeContext} {color : CostStaticColor}
    {outer : List TypeExpr}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    (leftChildren : CostRegionBoundaryTrees source targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees source targetFree color
      rightNode.finiteBoundaryTable)
    (_sourceSortEq : leftNode.sourceSort = rightNode.sourceSort)
    (planStep : staticLift.Edge leftNode.plan.decoration
      rightNode.plan.decoration leftChildren.decorations
        rightChildren.decorations)
    (_children : ∀ targetIndex,
      CostRegionTreeTransport source staticLift targetFree
        (leftChildren.getDecoration
          ((staticLift.boundaryMap planStep).pullback targetIndex)).tree
        (rightChildren.getDecoration targetIndex).tree),
    (∀ targetIndex, Nonempty
      (CostRegionTreeNormalizationAlignment source kernel targetFree
        (leftChildren.getDecoration
          ((staticLift.boundaryMap planStep).pullback targetIndex)).tree
        (rightChildren.getDecoration targetIndex).tree)) →
      Nonempty (CostRegionRootNormalizationBridge source kernel targetFree
        (CostRegionTree.static (outer := outer) leftNode leftChildren)
        (CostRegionTree.static (outer := outer) rightNode rightChildren))

mutual

  /-- Once static roots close locally, every proof-relevant structural tree
  transport has an exact hereditary normalization alignment.

  This is a theorem about the structural transport semantics.  It does not
  by itself tie the static edges occurring below the root to some separately
  supplied top-level authored occurrence; generator classifiers must retain
  and prove that occurrence-localization evidence independently. -/
  theorem CostRegionTreeTransport.nonemptyNormalizationAlignment
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {staticLift : CostStaticPlanLift source}
      (staticClosed : CostStaticTransportNormalizationClosed source kernel
        staticLift)
      {targetFree : FreeTypeContext}
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      {left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType}
      {right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType}
      (transport : CostRegionTreeTransport source staticLift targetFree left
        right) :
      Nonempty (CostRegionTreeNormalizationAlignment source kernel targetFree
        left right) :=
    match transport with
    | .refl tree =>
        ⟨CostRegionTreeNormalizationAlignment.refl tree⟩
    | .static leftNode rightNode leftChildren rightChildren sourceSortEq
        planStep children => by
        have childAlignments := fun targetIndex =>
          CostRegionTreeTransport.nonemptyNormalizationAlignment staticClosed
            (children targetIndex)
        obtain ⟨bridge⟩ := staticClosed leftNode rightNode leftChildren
          rightChildren sourceSortEq planStep children childAlignments
        exact ⟨bridge.toTreeAlignment⟩
    | .neutralApplicationOrdinary membership notBareCollection constructor
        materializes neutral ordinary leftChildren rightChildren arguments => by
        obtain ⟨argumentAlignment⟩ :=
          CostRegionArgumentTreesTransport.nonemptyNormalizationAlignment
            staticClosed arguments
        exact ⟨CostRegionTreeNormalizationAlignment.neutralApplicationOrdinary
          membership notBareCollection constructor materializes neutral
          ordinary leftChildren rightChildren argumentAlignment⟩
    | .neutralApplicationQuote membership notBareCollection constructor
        materializes neutral quoted leftChildren rightChildren arguments => by
        obtain ⟨argumentAlignment⟩ :=
          CostRegionArgumentTreesTransport.nonemptyNormalizationAlignment
            staticClosed arguments
        exact ⟨CostRegionTreeNormalizationAlignment.neutralApplicationQuote
          membership notBareCollection constructor materializes neutral
          quoted leftChildren rightChildren argumentAlignment⟩
    | .lambda leftTree rightTree body => by
        obtain ⟨bodyAlignment⟩ :=
          CostRegionTreeTransport.nonemptyNormalizationAlignment staticClosed
            body
        exact ⟨CostRegionTreeNormalizationAlignment.lambda leftTree
          rightTree bodyAlignment⟩
    | .multiLambda leftTree rightTree body => by
        obtain ⟨bodyAlignment⟩ :=
          CostRegionTreeTransport.nonemptyNormalizationAlignment staticClosed
            body
        exact ⟨CostRegionTreeNormalizationAlignment.multiLambda leftTree
          rightTree bodyAlignment⟩
    | .substBody leftTree rightTree replacementTree body => by
        obtain ⟨bodyAlignment⟩ :=
          CostRegionTreeTransport.nonemptyNormalizationAlignment staticClosed
            body
        exact ⟨CostRegionTreeNormalizationAlignment.subst leftTree
          rightTree replacementTree replacementTree bodyAlignment
          (.refl replacementTree)⟩
    | .substReplacement bodyTree leftTree rightTree replacement => by
        obtain ⟨replacementAlignment⟩ :=
          CostRegionTreeTransport.nonemptyNormalizationAlignment staticClosed
            replacement
        exact ⟨CostRegionTreeNormalizationAlignment.subst bodyTree bodyTree
          leftTree rightTree (.refl bodyTree) replacementAlignment⟩
    | .collection leftChildren rightChildren elements => by
        obtain ⟨elementAlignment⟩ :=
          CostRegionElementTreesTransport.nonemptyNormalizationAlignment
            staticClosed elements
        exact ⟨CostRegionTreeNormalizationAlignment.collection leftChildren
          rightChildren elementAlignment⟩

  /-- Mutual argument-spine assembly for exact hereditary alignment. -/
  theorem CostRegionArgumentTreesTransport.nonemptyNormalizationAlignment
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {staticLift : CostStaticPlanLift source}
      (staticClosed : CostStaticTransportNormalizationClosed source kernel
        staticLift)
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      {left : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters}
      {right : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters}
      (transport : CostRegionArgumentTreesTransport source staticLift
        targetFree left right) :
      Nonempty (CostRegionArgumentTreesNormalizationAlignment source kernel
        targetFree left right) :=
    match transport with
    | .nil => ⟨CostRegionArgumentTreesNormalizationAlignment.nil⟩
    | .cons leftRepresentation rightRepresentation parameterType leftHead
        rightHead leftTail rightTail head tail => by
        obtain ⟨headAlignment⟩ :=
          CostRegionTreeTransport.nonemptyNormalizationAlignment staticClosed
            head
        obtain ⟨tailAlignment⟩ :=
          CostRegionArgumentTreesTransport.nonemptyNormalizationAlignment
            staticClosed tail
        exact ⟨CostRegionArgumentTreesNormalizationAlignment.cons
          leftRepresentation rightRepresentation parameterType leftHead
          rightHead leftTail rightTail headAlignment tailAlignment⟩

  /-- Mutual collection-spine assembly for exact hereditary alignment. -/
  theorem CostRegionElementTreesTransport.nonemptyNormalizationAlignment
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {staticLift : CostStaticPlanLift source}
      (staticClosed : CostStaticTransportNormalizationClosed source kernel
        staticLift)
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      {left : CostRegionElementTrees source targetFree available outer
        leftElements elementType}
      {right : CostRegionElementTrees source targetFree available outer
        rightElements elementType}
      (transport : CostRegionElementTreesTransport source staticLift targetFree
        left right) :
      Nonempty (CostRegionElementTreesNormalizationAlignment source kernel
        targetFree left right) :=
    match transport with
    | .nil available outer elementType =>
        ⟨CostRegionElementTreesNormalizationAlignment.nil available outer
          elementType⟩
    | .cons leftHead rightHead leftTail rightTail head tail => by
        obtain ⟨headAlignment⟩ :=
          CostRegionTreeTransport.nonemptyNormalizationAlignment staticClosed
            head
        obtain ⟨tailAlignment⟩ :=
          CostRegionElementTreesTransport.nonemptyNormalizationAlignment
            staticClosed tail
        exact ⟨CostRegionElementTreesNormalizationAlignment.cons leftHead
          rightHead leftTail rightTail headAlignment tailAlignment⟩

end

end Mettapedia.GSLT.LanguageDef
