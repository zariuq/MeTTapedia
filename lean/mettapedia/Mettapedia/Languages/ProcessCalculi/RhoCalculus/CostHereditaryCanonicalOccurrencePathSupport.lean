import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportPathSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalOccurrenceSafe
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryTreeReflectiveSupport

/-!
# Path-indexed support preservation for hereditary rho frames

This module applies binder-free path-indexed reflective substitution to the
canonical target frame constructed by a rho Cost static node.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open CostStaticRegionNode

/-- Casting an occurrence across a root-pattern equality keeps its context. -/
private theorem castRoot_context {left right : Pattern} (equal : left = right)
    (occurrence : CostStaticFVarOccurrence left) :
    (CostStaticFVarOccurrence.castRoot equal occurrence).context =
      occurrence.context := by
  cases equal
  rfl

theorem rhoCostCanonicalOccurrenceAvailable_eq_pathAvailable
    (available : List TypeExpr) : ∀ context : OneHoleContext,
      rhoCostCanonicalOccurrenceAvailable available context =
        reflectiveOccurrenceAvailable rhoCIGSLT.costWholeReflectionProfile
          available context
  | .hole => rfl
  | .apply _ _ inner _ =>
      rhoCostCanonicalOccurrenceAvailable_eq_pathAvailable _ inner
  | .lambda _ inner =>
      rhoCostCanonicalOccurrenceAvailable_eq_pathAvailable available inner
  | .multiLambda _ _ inner =>
      rhoCostCanonicalOccurrenceAvailable_eq_pathAvailable available inner
  | .substBody inner _ =>
      rhoCostCanonicalOccurrenceAvailable_eq_pathAvailable available inner
  | .substReplacement _ inner =>
      rhoCostCanonicalOccurrenceAvailable_eq_pathAvailable available inner
  | .collection _ _ inner _ _ =>
      rhoCostCanonicalOccurrenceAvailable_eq_pathAvailable available inner

theorem CostStaticRegionNode.canonicalizeReifiedTargetFrame_binderFree
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory) :
    ReflectiveSubstitutionBinderFree
        (node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)) = true := by
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment]
  have sourceFrameFree :=
    rhoReflectiveSubstitutionBinderFree_canonicalizeByDepths
      (sourceSemanticPatternKeyAt node environment)
        node.targetBound.length 0 (node.reifiedSourceFrame environment).1
          (reifiedSourceFrame_binderFree node environment)
  have mappedFrameFree : ReflectiveSubstitutionBinderFree
      (mapPattern (color.symbols rhoCIGSLT)
        (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation node.targetBound.length 0
          (node.reifiedSourceFrame environment).1)) = true := by
    rw [rhoReflectiveSubstitutionBinderFree_mapPattern]
    exact sourceFrameFree
  rw [rhoReflectiveSubstitutionBinderFree_thickenAmbientBVars]
  exact mappedFrameFree

theorem rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path :
    RhoCostStaticReflectiveSupportPreserving rhoHereditaryStaticNormalizer := by
  intro color targetFree node values support available binderImage
    childrenPreserve inputSafe
  change (CostStaticRegionNode.normalizeHereditary node
      values).2.1.1.ReflectiveSupportSafeAt
    rhoCIGSLT.costWholeReflectionProfile support available binderImage
  let packed := node.semanticAtomEnvironment values
  let inventory := packed.1
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  obtain ⟨callerTyped, callerSafe⟩ :=
    canonicalizeReifiedTargetFrame_supportSafeAt_quoteLocalGCS node values
      inventory support available binderImage childrenPreserve inputSafe
  obtain ⟨actualTyped, actualSafe⟩ :=
    canonicalizeReifiedTargetFrame_ofInventory_supportSafe node values
      inventory
  have actualSafe' : callerTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile environment.restorationSupport
      node.targetBound id :=
    actualSafe.castTyping
  have frameFree : ReflectiveSubstitutionBinderFree
      (node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)) = true :=
    canonicalizeReifiedTargetFrame_binderFree node environment
  let Root : String → Type := fun name =>
    { occurrence : CostStaticFVarOccurrence
        (node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)) // occurrence.name = name }
  let rootAvailable : {name : String} → Root name → List TypeExpr :=
    fun {_name} root =>
      rhoCostCanonicalOccurrenceAvailable available root.1.context
  let embed : (occurrence : CostStaticFVarOccurrence
      (node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation))) → Root occurrence.name :=
    fun occurrence => ⟨occurrence, rfl⟩
  have embedAvailable : ∀ occurrence,
      rootAvailable (embed occurrence) =
        reflectiveOccurrenceAvailable rhoCIGSLT.costWholeReflectionProfile
          available occurrence.context := by
    intro occurrence
    exact rhoCostCanonicalOccurrenceAvailable_eq_pathAvailable available
      occurrence.context
  have valuesSafe : ∀ {name type}
      (lookup : environment.atomFreeContext name = some type)
      (root : Root name),
      (environment.restorationSupportedOpenAssignment.typed
          lookup).ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support
          (rootAvailable root) binderImage := by
    intro name type lookup root
    rcases root with ⟨occurrence, occurrenceName⟩
    subst name
    let rawOccurrence : CostStaticFVarOccurrence
        (node.thinning.thickenAmbientBVars 0
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (sourceSemanticPatternKeyAt node environment)
              rhoReflectivePresentation node.targetBound.length 0
              (node.reifiedSourceFrame environment).1))) :=
      CostStaticFVarOccurrence.castRoot
        (canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
          environment) occurrence
    have rawSafe :=
      mappedThickenedCanonicalOccurrence_assignmentSafeAt node values inventory
        support available binderImage childrenPreserve inputSafe rawOccurrence
          (by simpa [rawOccurrence] using lookup)
    simpa [rootAvailable, rawOccurrence, castRoot_context] using rawSafe
  obtain ⟨outputTyped, outputSafe⟩ :=
    callerSafe.substitutePreservingReflectiveSupportAtPaths
      environment.restorationSupportedOpenAssignment.toSupportedAssignment
      rho_costWholeLanguage_labelDeterministic
      rho_costWholeLanguage_collectionChoiceDeterministic
      actualSafe' frameFree [] (by simp) rootAvailable embed embedAvailable
        valuesSafe
  exact outputSafe.castTyping

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
