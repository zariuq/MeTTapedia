import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRestorationClosureCanary

/-!
# Canary for the rho static-to-structural atom terminal

The established base Quote/Drop fixture is reclosed through the general
canonical-atom terminal.  This checks that the terminal consumes the actual
finite environment selected by a compiled static node rather than a hand-
written equality of final normal forms.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary

/-- The breadth Quote/Drop node's reified frame selects one source-variable
atom for any complete value assignment. -/
noncomputable def rhoBreadthBaseRedexA_canonicalAtomWitness
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base
      rhoCutOrderFree rhoBreadthBaseRedexANode.finiteBoundaryTable) :
    let environment := CostStaticAtomEnvironment.ofInventory
      (rhoBreadthBaseRedexANode.semanticAtomEnvironment values).1
    Σ slot : Fin environment.atomCount,
      PLift ((rhoBreadthBaseRedexANode.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]]) ×
      PLift ((.fvar "a" : Pattern) = environment.restore
        rhoBreadthBaseRedexANode.targetBound
          (.fvar (environment.atomName slot))) := by
  let inventory := (rhoBreadthBaseRedexANode.semanticAtomEnvironment values).1
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  have sourceMembership : costRegionSourceVariableName "a" ∈
      rhoBreadthBaseRedexANode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthBaseRedexANode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  let occurrenceExists := rhoBreadthBaseRedexANode.skeleton_fvar_covered
    (costRegionSourceVariableName "a") sourceMembership
  let occurrence := Classical.choose occurrenceExists
  have occurrenceName := Classical.choose_spec occurrenceExists
  have slotExists := environment.slotOfName?_isSome_of_occurrence occurrence
  let slot := (environment.slotOfName? occurrence.name).get slotExists
  have selectedAtOccurrence : environment.slotOfName? occurrence.name =
      some slot := (Option.some_get slotExists).symm
  have selected : environment.slotOfName? (costRegionSourceVariableName "a") =
      some slot := by
    rw [← occurrenceName]
    exact selectedAtOccurrence
  have reifiedSource :
      (rhoBreadthBaseRedexANode.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]] := by
    rw [rhoBreadthBaseRedexANode.reifiedSourceFrame_pattern]
    change environment.reify
      (.apply "NQuote"
        [.apply "PDrop" [.fvar (costRegionSourceVariableName "a")]]) = _
    simp [CostStaticAtomEnvironment.reify,
      CostStaticAtomEnvironment.reifyName, selected,
      rhoReflectivePresentation]
  refine ⟨slot, ⟨reifiedSource⟩, ⟨?_⟩⟩
  · exact
      ((Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.quoteDropSourceVariableSemanticAtomJoinWithInventory
        rhoBreadthBaseRedexANode values inventory occurrence "a"
          occurrenceName slot selectedAtOccurrence reifiedSource).rightFactors :
        (.fvar "a" : Pattern) = environment.restore
          rhoBreadthBaseRedexANode.targetBound
            (.fvar (environment.atomName slot)))

/-- The generic static-to-structural terminal reconstructs the exact
Quote/Drop atom join used by the hereditary executor. -/
noncomputable def rhoBreadthBaseRedexAJoin_viaCanonicalAtom :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.normalizeHereditary
        rhoBreadthBaseRedexANode
        (TypedCostRegionBoundaryTable.Values.original
          rhoBreadthBaseRedexANode.finiteBoundaryTable)).1
      (.fvar "a") := by
  obtain ⟨slot, canonicalFrame, rightFactors⟩ :=
    rhoBreadthBaseRedexA_canonicalAtomWitness
      (TypedCostRegionBoundaryTable.Values.original
        rhoBreadthBaseRedexANode.finiteBoundaryTable)
  rcases canonicalFrame with ⟨reifiedFrame⟩
  rcases rightFactors with ⟨rightFactors⟩
  have canonicalFrame :=
    CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
      rhoBreadthBaseRedexANode _ slot reifiedFrame
  exact rhoCanonicalAtomSemanticJoin rhoBreadthBaseRedexANode
    (TypedCostRegionBoundaryTable.Values.original
      rhoBreadthBaseRedexANode.finiteBoundaryTable)
    slot canonicalFrame rightFactors

theorem rhoBreadthBaseRedexA_normalize_viaCanonicalAtom :
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.normalizeHereditary
      rhoBreadthBaseRedexANode
      (TypedCostRegionBoundaryTable.Values.original
        rhoBreadthBaseRedexANode.finiteBoundaryTable)).1 = .fvar "a" :=
  rhoBreadthBaseRedexAJoin_viaCanonicalAtom.results_eq

/-- Structural free-variable endpoint exposed by the base Quote/Drop frame. -/
def rhoBreadthATree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] (.fvar "a")
      (.base (costBaseSortName "Name")) :=
  .fvar (by simp [rhoCutOrderFree, FreeTypeContext.ofList])

/-- The full root bridge for the established Quote/Drop fixture is obtained
through the proof-relevant atom branch of `RhoCollapsingLeafExposure`, not
from a final equality. -/
noncomputable def rhoBreadthBaseRedexABridge_viaQuoteDropAtom :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      rhoBreadthBaseRedexAStaticTree rhoBreadthATree := by
  let values := rhoBreadthBaseRedexAChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  obtain ⟨slot, reifiedFrame, rightFactors⟩ :=
    rhoBreadthBaseRedexA_canonicalAtomWitness values
  rcases reifiedFrame with ⟨reifiedFrame⟩
  rcases rightFactors with ⟨rightFactors⟩
  let exposure : RhoCollapsingLeafExposure
      rhoBreadthBaseRedexANode rhoBreadthBaseRedexAChildren rhoBreadthATree :=
    .atom slot
      (CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
        rhoBreadthBaseRedexANode _ slot reifiedFrame)
      (by simpa [rhoBreadthATree, CostRegionTree.normalize] using rightFactors)
  exact exposure.toRootBridge

theorem rhoBreadthBaseRedexABridge_viaQuoteDropAtom_results_eq :
    (rhoBreadthBaseRedexAStaticTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoBreadthATree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  rhoBreadthBaseRedexABridge_viaQuoteDropAtom.toTreeAlignment.normalize_pattern_eq

/-! ## Foreign-boundary Quote/Drop control

The wrapped Quote/Drop shell below contains the established base-colour
Quote/Drop child as a certified foreign boundary.  Its hereditary value is the
free name `a`; the enclosing wrapped shell then collapses to that value.  This
is the smallest production-shaped regression for the support-independent
`boundarySourceVariable` constructor.
-/

private theorem rhoForeignRule_mem (index : Nat) (inBounds : index < 6) :
    rhoCalc.terms[index]'(by simp [rhoCalc]; omega) ∈ rhoCalc.terms :=
  List.getElem_mem _

private def rhoForeignDropConstructor :
    AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[1], rhoForeignRule_mem 1 (by omega)⟩

private theorem rhoForeignDrop_selected :
    rhoForeignDropConstructor ∈
      rhoContinuationRetyping.wrappedConstructors := by
  apply (rhoContinuationRetyping.mem_wrappedConstructors_iff
    rhoForeignDropConstructor).2
  constructor <;> decide

private def rhoForeignQuoteConstructor :
    AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[2], rhoForeignRule_mem 2 (by omega)⟩

private theorem rhoForeignQuote_selected :
    rhoForeignQuoteConstructor ∈
      rhoContinuationRetyping.wrappedConstructors := by
  apply (rhoContinuationRetyping.mem_wrappedConstructors_iff
    rhoForeignQuoteConstructor).2
  constructor <;> decide

private def rhoForeignWrappedDropDeclared :
    rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.wrapped rhoForeignDropConstructor, rhoForeignDrop_selected⟩

private def rhoForeignWrappedQuoteDeclared :
    rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.wrapped rhoForeignQuoteConstructor, rhoForeignQuote_selected⟩

private theorem rhoForeignWrappedDropRole :
    rhoCIGSLT.declaredCostConstructorRole rhoForeignWrappedDropDeclared =
      .static .wrapped := rfl

private theorem rhoForeignWrappedQuoteRole :
    rhoCIGSLT.declaredCostConstructorRole rhoForeignWrappedQuoteDeclared =
      .static .wrapped := rfl

private def rhoForeignWrappedDropPreimage :
    CostStaticConstructorPreimage rhoCIGSLT .wrapped
      rhoForeignWrappedDropDeclared :=
  costStaticConstructorPreimage rhoCIGSLT .wrapped
    rhoForeignWrappedDropDeclared rhoForeignWrappedDropRole

private def rhoForeignWrappedQuotePreimage :
    CostStaticConstructorPreimage rhoCIGSLT .wrapped
      rhoForeignWrappedQuoteDeclared :=
  costStaticConstructorPreimage rhoCIGSLT .wrapped
    rhoForeignWrappedQuoteDeclared rhoForeignWrappedQuoteRole

private theorem rhoForeignWrappedDrop_notBare :
    ¬ UsesBareCollection
      rhoForeignWrappedDropPreimage.sourceConstructor.1 := by
  simp [rhoForeignWrappedDropPreimage, costStaticConstructorPreimage,
    rhoForeignWrappedDropDeclared, rhoForeignDropConstructor,
    UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
    TypeExpr.baseType]

private theorem rhoForeignWrappedQuote_notBare :
    ¬ UsesBareCollection
      rhoForeignWrappedQuotePreimage.sourceConstructor.1 := by
  simp [rhoForeignWrappedQuotePreimage, costStaticConstructorPreimage,
    rhoForeignWrappedQuoteDeclared, rhoForeignQuoteConstructor,
    UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
    TypeExpr.baseType]

private theorem rhoForeignBaseQuoteOutsideWrapped :
    rhoCIGSLT.declaredCostConstructorRole rhoBreadthBaseQuoteDeclared ≠
      .static .wrapped := by
  rw [rhoBreadthBaseQuoteRole]
  decide

private noncomputable def rhoForeignBoundaryPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] outer rhoBreadthRedexA (.base "Name") :=
  .boundaryApplication rhoBreadthBaseQuoteDeclared rfl
    rhoForeignBaseQuoteOutsideWrapped rhoBreadthBoundaryWitnessA
    rhoBreadthBoundaryWitnessA_spec

private noncomputable def rhoForeignWrappedDropPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] outer rhoBreadthLeftProcess (.base "Proc") := by
  apply CostStaticRegionPlan.application rhoForeignWrappedDropDeclared rfl
    rhoForeignWrappedDropRole rhoForeignWrappedDropPreimage
  · exact rhoForeignWrappedDrop_notBare
  · exact .cons (by trivial) rfl
      (rhoForeignBoundaryPlan
        (outer.comp
          (.apply (costWrappedConstructorName "PDrop") [] .hole [])))
      .nil

def rhoForeignBoundaryQuotePattern : Pattern :=
  .apply (costWrappedConstructorName "NQuote") [rhoBreadthLeftProcess]

private noncomputable def rhoForeignBoundaryQuotePlan :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] .hole rhoForeignBoundaryQuotePattern (.base "Name") := by
  apply CostStaticRegionPlan.application rhoForeignWrappedQuoteDeclared rfl
    rhoForeignWrappedQuoteRole rhoForeignWrappedQuotePreimage
  · exact rhoForeignWrappedQuote_notBare
  · exact .cons (by trivial) rfl
      (rhoForeignWrappedDropPlan
        (OneHoleContext.hole.comp
          (.apply (costWrappedConstructorName "NQuote") [] .hole [])))
      .nil

private theorem rhoForeignBoundaryQuote_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoForeignBoundaryQuotePattern (.base (costBaseSortName "Name")) := by
  apply HasType.constructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[2])
  · exact rhoCIGSLT.costWrappedConstructor_mem_costWhole
      rhoForeignQuoteConstructor rhoForeignQuote_selected
  · rw [usesBareCollection_costWrappedConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costWrappedQuoteConstructor_params]
    exact .cons (by trivial) rfl rhoBreadthLeftProcessNode.term.2.1 .nil

private theorem rhoForeignWrappedNameType :
    (.base (costBaseSortName "Name") : TypeExpr) =
      .base (CostStaticColor.wrapped.mapLangSort rhoCIGSLT rhoName).1 := by
  simp [CostStaticColor.symbols,
    costWrappedStaticSymbols, rhoCIGSLT, rhoIGSLT,
    rhoInteractivePresentation, rhoCalc, TypeDecl.plain, rhoName,
    show "Name" ≠ "Proc" by decide]

private def rhoForeignBoundaryQuoteTerm :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (CostStaticColor.wrapped.mapLangSort rhoCIGSLT rhoName) := by
  have typed : HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoForeignBoundaryQuotePattern
        (.base (CostStaticColor.wrapped.mapLangSort rhoCIGSLT rhoName).1) := by
    rw [← rhoForeignWrappedNameType]
    exact rhoForeignBoundaryQuote_typed
  refine ⟨rhoForeignBoundaryQuotePattern,
    ⟨⟨typed, rfl, rfl, typed.isWellScopedAt⟩, ?_⟩⟩
  intro declaration membership
  simp [rhoForeignBoundaryQuotePattern, rhoBreadthLeftProcess,
    rhoCutOrderWrappedDrop, rhoCutOrderBaseQuote, rhoCutOrderBaseDrop,
    binderSafeAt, binderSafeListAt]

noncomputable def rhoForeignBoundaryQuoteNode :
    CostStaticRegionNode rhoCIGSLT .wrapped rhoCutOrderFree :=
  CostStaticRegionNode.ofPlan rhoForeignBoundaryQuoteTerm.toCore
    rhoForeignBoundaryQuotePlan
    (by unfold rhoForeignBoundaryQuotePlan; rfl)

noncomputable def rhoForeignBoundaryQuoteChildren :
    CostRegionBoundaryTrees rhoCIGSLT rhoCutOrderFree .wrapped
      rhoForeignBoundaryQuoteNode.finiteBoundaryTable :=
  .cons rhoBreadthBoundaryChildA .nil

private theorem rhoForeignBoundaryQuoteNode_skeleton :
    rhoForeignBoundaryQuoteNode.skeleton.1 =
      .apply "NQuote"
        [.apply "PDrop"
          [.fvar (costRegionBoundaryVariableName
            rhoBreadthBoundaryWitnessA.typed.boundary)]] :=
  rfl

noncomputable def rhoForeignBoundaryQuoteView :
    CostStaticPlanContextInventoryView rhoCIGSLT .wrapped rhoCutOrderFree
      rhoBreadthRedexA rhoForeignBoundaryQuoteNode.skeleton.1
      rhoForeignBoundaryQuoteNode.finiteBoundaryTable.entries where
  view := .stopped
    { boundarySupport := []
      boundaryType := _
      content := rhoBreadthRedexA
      certified := rhoBreadthBoundaryWitnessA
      residual := .hole
      content_eq := rfl
      skeletonContext :=
        .apply "NQuote" [] (.apply "PDrop" [] .hole []) []
      abstract_eq := rhoForeignBoundaryQuoteNode_skeleton }
  entryEmbedding := .keep (.nil [])

noncomputable def rhoForeignBoundaryQuoteTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] []
      rhoForeignBoundaryQuotePattern (.base (costBaseSortName "Name")) :=
  .static rhoForeignBoundaryQuoteNode rhoForeignBoundaryQuoteChildren

/-- The foreign-boundary shell closes through the generic one-environment
boundary exposure, not through a fixture equality of final normal forms. -/
noncomputable def rhoForeignBoundaryQuoteBridge :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      rhoForeignBoundaryQuoteTree rhoBreadthFvarAStructuralTree := by
  let environment := rhoForeignBoundaryQuoteNode.normalizationEnvironment
    rhoHereditaryStaticNormalizer rhoForeignBoundaryQuoteChildren
  have membership : costRegionBoundaryVariableName
      rhoBreadthBoundaryWitnessA.typed.boundary ∈
        rhoForeignBoundaryQuoteNode.skeleton.1.freeFvarNames := by
    rw [rhoForeignBoundaryQuoteNode_skeleton]
    simp [Pattern.freeFvarNames]
  let occurrenceExists := rhoForeignBoundaryQuoteNode.skeleton_fvar_covered
    _ membership
  let occurrence := Classical.choose occurrenceExists
  have occurrenceName := Classical.choose_spec occurrenceExists
  let slotExists := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence occurrence)
  let slot := Classical.choose slotExists
  have selected := Classical.choose_spec slotExists
  have selectedBoundary : environment.slotOfName?
      (costRegionBoundaryVariableName
        rhoBreadthBoundaryWitnessA.typed.boundary) = some slot := by
    rw [← occurrenceName]
    exact selected
  have reifiedFrame :
      (rhoForeignBoundaryQuoteNode.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]] := by
    rw [rhoForeignBoundaryQuoteNode.reifiedSourceFrame_pattern]
    change environment.reify
      (.apply "NQuote"
        [.apply "PDrop"
          [.fvar (costRegionBoundaryVariableName
            rhoBreadthBoundaryWitnessA.typed.boundary)]]) = _
    simp [CostStaticAtomEnvironment.reify,
      CostStaticAtomEnvironment.reifyName, selectedBoundary,
      rhoReflectivePresentation]
  let exposure := RhoCollapsingLeafExposure.boundarySourceVariable
    rhoForeignBoundaryQuoteNode rhoForeignBoundaryQuoteChildren
    rhoForeignBoundaryQuoteView ⟨0, by decide⟩ occurrence
    (by exact occurrenceName) "a" rhoBreadthFvarAStructuralTree slot selected
    (CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
      rhoForeignBoundaryQuoteNode environment slot reifiedFrame)
    rhoBreadthStoppedChildToFvarAlignment
  exact exposure.toRootBridge

theorem rhoForeignBoundaryQuoteBridge_normalize_pattern_eq :
    (rhoForeignBoundaryQuoteTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoBreadthFvarAStructuralTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  rhoForeignBoundaryQuoteBridge.toTreeAlignment.normalize_pattern_eq

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
