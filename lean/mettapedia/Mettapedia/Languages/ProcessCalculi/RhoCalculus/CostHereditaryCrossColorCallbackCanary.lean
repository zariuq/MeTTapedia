import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

/-!
# Callback-sufficiency canary

The recursive middle of the cross-colour hinge needs exactly one service
from the smaller-pair callback: at a stopped boundary, the boundary
content's hereditary normalized compact pattern must equal the partner's.
The compact `CostCanonicalPairElaboration` returned by `RhoPairCloseSmaller`
retains the complete `CostRegionTreeNormalizationAlignment`, whose
eliminator `CostRegionTreeNormalizationAlignment.normalize_pattern_eq`
produces precisely that equality between the elaborated trees.

This canary proves the consumer-facing sufficiency lemma directly: from a
`closeSmaller` hypothesis on a canonical pair of smaller payloads, any two
trees of those payloads have equal normalized patterns — via
`normalize_pattern_eq_of_unambiguous` bridges on both sides and the compact
alignment in the middle.  No richer recursive result is assumed, so if the
descend ever lacks parent-cospan actions (a *different* question from
normal equality), the failure point here is isolated.

Named after the audit directive of 2026-08-17
(post-hinge construction roadmap, phase 1.1).
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostHereditaryCrossColorCallbackCanary

/-- **The compact smaller-pair callback suffices for boundary normal
equality.**

For any two smaller canonically equal payloads, the `closeSmaller` callback
elaborates a pair whose alignment proves their hereditary normalized
patterns equal; by tree uniqueness we may use any two trees of the
payloads — e.g. the boundary child tree extracted from a view and the
partner's own tree. -/
theorem normalize_pattern_eq_of_closeSmaller_alignment
    {declarationColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {measure : Nat} {childType : TypeExpr}
    {leftPayload rightPayload : Pattern}
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree measure)
    {leftTree : CostRegionTree rhoCIGSLT targetFree available outer
      leftPayload childType}
    {rightTree : CostRegionTree rhoCIGSLT targetFree available outer
      rightPayload childType}
    (leftWellSorted :
      ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available childType leftPayload)
    (rightWellSorted :
      ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available childType rightPayload)
    (canonical :
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    (smaller : sizeOf leftPayload + sizeOf rightPayload < measure)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible childType)
    (leftObject : WellSorted.isObjectPattern leftPayload = true)
    (rightObject : WellSorted.isObjectPattern rightPayload = true) :
    (leftTree.normalize (normalizeStatic :=
        rhoHereditaryNormalizationKernel.normalize)).pattern =
      (rightTree.normalize (normalizeStatic :=
        rhoHereditaryNormalizationKernel.normalize)).pattern := by
  obtain ⟨elaboration⟩ :=
    closeSmaller (childOuter := outer) leftWellSorted rightWellSorted
      canonical smaller admissible
  have alignmentEq := elaboration.alignment.normalize_pattern_eq
  exact (CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel leftTree elaboration.leftTree
      leftObject).trans
    (alignmentEq.trans
      (CostRegionTree.normalize_pattern_eq_of_unambiguous
        CostCanonicalLaws.rho_unambiguousStaticDecomposition
        rhoHereditaryNormalizationKernel elaboration.rightTree rightTree
        rightObject))

end CostHereditaryCrossColorCallbackCanary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
