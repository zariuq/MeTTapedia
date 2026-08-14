import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalOrderAgnosticDepths

/-!
# Bound-variable exposure for hereditary rho Cost normalization

When ordinary canonicalization of an atomized source frame is a bound
variable, semantic-key ordering cannot change that leaf.  The Cost map and
binder thinning determine its exact target index, and semantic-atom
restoration leaves the bound variable untouched.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A source-frame canonical collapse to a bound variable determines the
exact hereditary target normal form.  No semantic atom or recursive child is
involved in this terminal. -/
theorem CostStaticRegionNode.normalizeHereditaryRawWithInventory_bvar_of_sourceCanonical
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (sourceIndex : Nat)
    (collapse :
      canonicalize rhoReflectivePresentation
          (node.reifiedSourceFrame
            (CostStaticAtomEnvironment.ofInventory inventory)).1 =
        .bvar sourceIndex) :
    node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      .bvar (node.thinning.embedIndexAt 0 sourceIndex) := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  unfold CostStaticRegionNode.normalizeHereditaryRawWithInventory
  change environment.restore node.targetBound
      (node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)) = _
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    node environment]
  rw [canonicalizeByDepths_eq_bvar_of_canonicalize_eq
    (CostStaticRegionNode.sourceSemanticPatternKeyAt node environment)
      rhoReflectivePresentation node.targetBound.length 0 collapse]
  simp [mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticAtomEnvironment.restore, CostStaticAtomEnvironment.restoreAt,
    ReflectiveContextSupport.substituteAt]

/-- The executable total-inventory normalizer inherits the same rigid bound
variable terminal. -/
theorem CostStaticRegionNode.normalizeHereditary_bvar_of_sourceCanonical
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (sourceIndex : Nat)
    (collapse :
      canonicalize rhoReflectivePresentation
          (node.reifiedSourceFrame
            (CostStaticAtomEnvironment.ofInventory
              (node.semanticAtomEnvironment values).1)).1 =
        .bvar sourceIndex) :
    (rhoHereditaryStaticNormalizer node values).1 =
      .bvar (node.thinning.embedIndexAt 0 sourceIndex) := by
  unfold rhoHereditaryStaticNormalizer CostStaticRegionNode.normalizeHereditary
  rw [CostStaticRegionNode.normalizeHereditaryWithInventory_pattern]
  exact
    CostStaticRegionNode.normalizeHereditaryRawWithInventory_bvar_of_sourceCanonical
      node values (node.semanticAtomEnvironment values).1 sourceIndex collapse

namespace RhoCollapsingLeafExposure

/-- Construct the rigid bound-variable exposure directly from the ordinary
canonical form of the atomized source frame.  The only endpoint premise is
the structural tree's exact normal form; the static equation is derived by
the keyed/plain order-agnostic bridge above. -/
noncomputable def rigidBVarOfSourceCanonical
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (sourceIndex : Nat)
    (collapse :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      canonicalize rhoReflectivePresentation
          (node.reifiedSourceFrame
            (CostStaticAtomEnvironment.ofInventory
              (node.semanticAtomEnvironment values).1)).1 =
        .bvar sourceIndex)
    (rightNormal :
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      .bvar (node.thinning.embedIndexAt 0 sourceIndex)) :
    RhoCollapsingLeafExposure node children right := by
  exact .rigidBVar (node.thinning.embedIndexAt 0 sourceIndex)
    (CostStaticRegionNode.normalizeHereditary_bvar_of_sourceCanonical node
      (children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)) sourceIndex
      collapse)
    rightNormal

end RhoCollapsingLeafExposure

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
