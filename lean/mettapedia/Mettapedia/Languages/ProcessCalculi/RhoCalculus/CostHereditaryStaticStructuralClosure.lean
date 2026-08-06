import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRestorationClosure

/-!
# Static-to-structural hereditary closure for rho Cost

Reflective collapse can expose one recursively normalized semantic atom as
the complete result of a static region.  The exposed value may elaborate as
a structural tree: Quote/Drop can reveal a free name, and parallel singleton
collapse can reveal a neutral process application.  The bridge below covers
both forms without inspecting the atom's compact shape.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode

/-- A reified Quote/Drop shell canonicalizes to its selected semantic atom,
independently of the target binder context. -/
theorem CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (slot : Fin environment.atomCount)
    (reifiedFrame : (node.reifiedSourceFrame environment).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar (environment.atomName slot)]]) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      .fvar (environment.atomName slot) := by
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment, reifiedFrame]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    rhoReflectivePresentation, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars]

/-- A reified bare-parallel singleton canonicalizes to its selected semantic
atom, independently of the semantic key: sorting a singleton has no choice. -/
theorem CostStaticRegionNode.canonicalizeReifiedTargetFrame_parallelSingleton_atom
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (slot : Fin environment.atomCount)
    (reifiedFrame : (node.reifiedSourceFrame environment).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.fvar (environment.atomName slot)] none) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      .fvar (environment.atomName slot) := by
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment, reifiedFrame]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    rhoReflectivePresentation, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars]

/-- A reified bare-parallel singleton whose payload is a bound variable
canonicalizes to the mapped, binder-reinserted variable itself.  Unlike the
atom theorem above, this case has no finite free-variable slot. -/
theorem CostStaticRegionNode.canonicalizeReifiedTargetFrame_parallelSingleton_bvar
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (sourceIndex : Nat)
    (reifiedFrame : (node.reifiedSourceFrame environment).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.bvar sourceIndex] none) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT) (.bvar sourceIndex)) := by
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment, reifiedFrame]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    rhoReflectivePresentation]

/-- Hereditary evaluation of the same rigid singleton restores no semantic
atom: supported substitution preserves the surviving bound index. -/
theorem CostStaticRegionNode.normalizeHereditaryRawWithInventory_parallelSingleton_bvar
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (sourceIndex : Nat)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.bvar sourceIndex] none) :
    node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT) (.bvar sourceIndex)) := by
  unfold CostStaticRegionNode.normalizeHereditaryRawWithInventory
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  change environment.restore node.targetBound
      (node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)) = _
  have frame : (node.reifiedSourceFrame environment).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.bvar sourceIndex] none := by
    simpa only [environment] using reifiedFrame
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_parallelSingleton_bvar
    node environment sourceIndex frame]
  simp [CostStaticAtomEnvironment.restore,
    CostStaticAtomEnvironment.restoreAt,
    ReflectiveContextSupport.substituteAt, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars]

/-- A selected rho frame consisting of one bare-parallel semantic atom
evaluates to restoration of that atom.  Unlike the Quote/Drop companion, no
availability reset occurs; the exact target binder depth is retained by the
restoration operation. -/
theorem CostStaticRegionNode.normalizeHereditaryRawWithInventory_parallelSingleton_restore
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.fvar ((CostStaticAtomEnvironment.ofInventory inventory).atomName
          slot)] none) :
    node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      (CostStaticAtomEnvironment.ofInventory inventory).restore
        node.targetBound
        (.fvar ((CostStaticAtomEnvironment.ofInventory inventory).atomName
          slot)) := by
  rw [normalizeHereditaryRawWithInventory_eq_sourceAction node values
    inventory, reifiedFrame]
  unfold rhoCostStaticActionAt
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    rhoReflectivePresentation]
  unfold CostStaticAtomEnvironment.restore
    CostStaticAtomEnvironment.restoreAt
  change ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeLanguage
      (CostStaticAtomEnvironment.ofInventory inventory).restorationSupport
      (CostStaticAtomEnvironment.ofInventory inventory).restorationAssignment
      node.targetBound.length
      (node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (.fvar ((CostStaticAtomEnvironment.ofInventory inventory).atomName
            slot)))) = _
  simp [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]

/-- Total-inventory form of the bare-parallel singleton atom exposure. -/
theorem CostStaticRegionNode.normalizeHereditary_parallelSingleton_restore
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment values).1).atomCount)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1)).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.fvar ((CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1).atomName slot)] none) :
    (normalizeHereditary node values).1 =
      (CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1).restore node.targetBound
          (.fvar ((CostStaticAtomEnvironment.ofInventory
            (node.semanticAtomEnvironment values).1).atomName slot)) := by
  unfold normalizeHereditary
  rw [normalizeHereditaryWithInventory_pattern]
  exact normalizeHereditaryRawWithInventory_parallelSingleton_restore node
    values (node.semanticAtomEnvironment values).1 slot reifiedFrame

/-- A rho static frame whose canonical target frame is one selected atom
meets any result that factors through restoration of that same atom.

The finite inventory and atom position are retained.  Equality of the two
results is consequently derived by `PackedCostSemanticAtomJoin.results_eq`;
it is not stored as a premise. -/
def rhoCanonicalAtomSemanticJoinWithInventory
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount)
    (canonicalFrame :
      node.canonicalizeReifiedTargetFrame
          (CostStaticAtomEnvironment.ofInventory inventory)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((CostStaticAtomEnvironment.ofInventory inventory).atomName
          slot))
    {rightResult : Pattern}
    (rightFactors : rightResult =
      (CostStaticAtomEnvironment.ofInventory inventory).restore
        node.targetBound
        (.fvar ((CostStaticAtomEnvironment.ofInventory inventory).atomName
          slot))) :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (normalizeHereditaryWithInventory node values inventory).1
      rightResult where
  color := color
  targetFree := targetFree
  occurrences := node.plan.occurrences
  table := node.boundaryTable
  values := values
  root := node.skeleton.1
  inventory := inventory
  environment := CostStaticAtomEnvironment.ofInventory inventory
  bound := node.targetBound
  slot := slot
  leftFactors := by
    rw [normalizeHereditaryWithInventory_pattern]
    unfold Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.normalizeHereditaryRawWithInventory
    exact congrArg
      ((CostStaticAtomEnvironment.ofInventory inventory).restore
        node.targetBound) canonicalFrame
  rightFactors := rightFactors

/-- Total-inventory specialization of
`rhoCanonicalAtomSemanticJoinWithInventory`. -/
def rhoCanonicalAtomSemanticJoin
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment values).1).atomCount)
    (canonicalFrame :
      node.canonicalizeReifiedTargetFrame
          (CostStaticAtomEnvironment.ofInventory
            (node.semanticAtomEnvironment values).1)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1).atomName slot))
    {rightResult : Pattern}
    (rightFactors : rightResult =
      (CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1).restore node.targetBound
        (.fvar ((CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1).atomName slot))) :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (normalizeHereditary node values).1 rightResult := by
  unfold normalizeHereditary
  exact rhoCanonicalAtomSemanticJoinWithInventory node values
    (node.semanticAtomEnvironment values).1 slot canonicalFrame rightFactors

/-- Lift a selected canonical atom of one static rho root to the general
root-bridge carrier against an arbitrary structural tree. -/
noncomputable def rhoStaticRootBridgeOfCanonicalAtom
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment
        (children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1).atomCount)
    (canonicalFrame :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot))
    (rightFactors :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        environment.restore node.targetBound
          (.fvar (environment.atomName slot))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) node children) right := by
  let values := children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let join := rhoCanonicalAtomSemanticJoin node values slot canonicalFrame
    rightFactors
  refine .semanticAtom _ _ ?_
  exact join.transport (by
    rw [CostRegionTree.normalize_static_pattern]
    rfl) rfl

/-- Quote/Drop specialization of `rhoStaticRootBridgeOfCanonicalAtom`.
Callers supply the proof-relevant selected slot and the structural endpoint's
restoration factorization; the canonical-frame equation is derived here. -/
noncomputable def rhoStaticRootBridgeOfQuoteDropAtom
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment
        (children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1).atomCount)
    (reifiedFrame :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      (node.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]])
    (rightFactors :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        environment.restore node.targetBound
          (.fvar (environment.atomName slot))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) node children) right := by
  apply rhoStaticRootBridgeOfCanonicalAtom node children right slot
  · exact CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
      node _ slot reifiedFrame
  · exact rightFactors

/-- Bare-parallel singleton specialization of
`rhoStaticRootBridgeOfCanonicalAtom`.  This is the asymmetric terminal used
when a static process frame exposes a neutral recursively normalized child. -/
noncomputable def rhoStaticRootBridgeOfParallelSingletonAtom
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment
        (children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1).atomCount)
    (reifiedFrame :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      (node.reifiedSourceFrame environment).1 =
        .collection rhoReflectivePresentation.parallelCollection
          [.fvar (environment.atomName slot)] none)
    (rightFactors :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        environment.restore node.targetBound
          (.fvar (environment.atomName slot))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) node children) right := by
  apply rhoStaticRootBridgeOfCanonicalAtom node children right slot
  · exact
      CostStaticRegionNode.canonicalizeReifiedTargetFrame_parallelSingleton_atom
        node _ slot reifiedFrame
  · exact rightFactors

/-- Static-to-structural terminal for a collapse that exposes a rigid compact
leaf rather than a finite semantic atom.

Bound variables are the motivating case: they are preserved by supported
substitution at every depth but are deliberately absent from the free-variable
atom inventory.  The two factorization equations are supplied by the rho
collapse inversion, while `rigid` independently certifies that the common leaf
does not depend on a support assignment. -/
def rhoStaticRootBridgeOfRigidLeaf
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (leaf : Pattern)
    (rigid : ∀ support assignment depth,
      ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeLanguage
        support assignment depth leaf = leaf)
    (leftFactors :
      ((CostRegionTree.static (outer := leftOuter) node children).normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern = leaf)
    (rightFactors :
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern = leaf) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) node children) right :=
  .rigidLeaf _ _
    { leaf := leaf
      rigid := rigid
      leftFactors := leftFactors
      rightFactors := rightFactors }

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
