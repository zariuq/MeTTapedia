import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRestorationClosureCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairShapeCanary

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

/-- The source variable inside the breadth Quote/Drop frame, selected by its
exact two-layer zipper rather than by its spelling. -/
def rhoBreadthBaseRedexAOccurrence : CostStaticFVarOccurrence
    rhoBreadthBaseRedexANode.skeleton.1 where
  name := costRegionSourceVariableName "a"
  context := .apply "NQuote" [] (.apply "PDrop" [] .hole []) []
  selected := by
    rw [rhoBreadthBaseRedexANode_skeleton_pattern]
    exact .apply (.apply .here)

/-- Both semantic reification stages retain the selected occurrence zipper.
The leaf name enters the common semantic namespace, but the causal position
cannot collapse to the root occurrence. -/
theorem rhoBreadthBaseRedexA_commonReification_preservesOccurrence :
    let values := TypedCostRegionBoundaryTable.Values.original
      rhoBreadthBaseRedexANode.finiteBoundaryTable
    let environment := (rhoBreadthBaseRedexANode.semanticAtomEnvironment
      values).2
    let cospan := environment.semanticKeyCospan environment
    ∃ slot : Fin environment.atomCount,
      environment.slotOfName? rhoBreadthBaseRedexAOccurrence.name =
          some slot ∧
      (cospan.reifyEnvironmentOccurrence environment cospan.leftSlot
          rhoBreadthBaseRedexAOccurrence).name =
        cospan.commonAtomName (cospan.leftSlot slot) ∧
      (cospan.reifyEnvironmentOccurrence environment cospan.leftSlot
          rhoBreadthBaseRedexAOccurrence).context =
        .apply "NQuote" [] (.apply "PDrop" [] .hole []) [] ∧
      (cospan.reifyEnvironmentOccurrence environment cospan.leftSlot
          rhoBreadthBaseRedexAOccurrence).context ≠ .hole := by
  dsimp only
  let values := TypedCostRegionBoundaryTable.Values.original
    rhoBreadthBaseRedexANode.finiteBoundaryTable
  let environment := (rhoBreadthBaseRedexANode.semanticAtomEnvironment
    values).2
  let cospan := environment.semanticKeyCospan environment
  obtain ⟨slot, selected⟩ := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence
      rhoBreadthBaseRedexAOccurrence)
  refine ⟨slot, selected, ?_, ?_, ?_⟩
  · exact cospan.reifyEnvironmentOccurrence_name_eq_commonAtomName
      environment cospan.leftSlot rhoBreadthBaseRedexAOccurrence slot selected
  · rfl
  · decide

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

private noncomputable def rhoForeignBoundaryQuoteStopped :
    CostStaticPlanStopped rhoCIGSLT .wrapped rhoCutOrderFree
      rhoBreadthRedexA rhoForeignBoundaryQuoteNode.skeleton.1 where
  boundarySupport := []
  boundaryType := _
  content := rhoBreadthRedexA
  certified := rhoBreadthBoundaryWitnessA
  certifies := rhoBreadthBoundaryWitnessA_spec
  residual := .hole
  content_eq := rfl
  skeletonContext :=
    .apply "NQuote" [] (.apply "PDrop" [] .hole []) []
  abstract_eq := rhoForeignBoundaryQuoteNode_skeleton

noncomputable def rhoForeignBoundaryQuoteView :
    CostStaticPlanContextInventoryView rhoCIGSLT .wrapped rhoCutOrderFree
      rhoBreadthRedexA rhoForeignBoundaryQuoteNode.skeleton.1
      rhoForeignBoundaryQuoteNode.finiteBoundaryTable.entries where
  view := .stopped rhoForeignBoundaryQuoteStopped
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
  have childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      rhoBreadthBoundaryChildA rhoBreadthFvarAStructuralTree := by
    refine .semanticAtom _ _ ?_
    exact rhoBreadthBaseRedexANodeSemanticAtomJoin.transport (by
        change (CostRegionTree.normalizeHereditary
            rhoBreadthBoundaryChildA).pattern =
          (CostStaticRegionNode.normalizeHereditary
            rhoBreadthBaseRedexANode
            (TypedCostRegionBoundaryTable.Values.original
              rhoBreadthBaseRedexANode.finiteBoundaryTable)).1
        exact rhoBreadthBoundaryChildA_normalizeHereditary.trans
          rhoBreadthBaseRedexANode_normalizeHereditary.symm) (by
        change (rhoBreadthFvarAStructuralTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .fvar "a"
        simp [rhoBreadthFvarAStructuralTree, CostRegionTree.normalize])
  let exposure :=
    RhoCollapsingLeafExposure.stoppedQuoteDropBoundaryElaborationAlignedSameSupport
    rhoForeignBoundaryQuoteNode rhoForeignBoundaryQuoteChildren
    rhoForeignBoundaryQuoteStopped (.keep (.nil [])) rfl
    rhoBreadthBoundaryChildA rhoBreadthFvarAStructuralTree
    rhoBreadthFvarAStructuralTree childAlignment rfl (by
      rw [rhoForeignBoundaryQuoteStopped.certified.targetSupport_eq]
      rfl)
  exact exposure.toRootBridge

theorem rhoForeignBoundaryQuoteBridge_normalize_pattern_eq :
    (rhoForeignBoundaryQuoteTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoBreadthFvarAStructuralTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  rhoForeignBoundaryQuoteBridge.toTreeAlignment.normalize_pattern_eq

/-- The foreign-boundary endpoint and its exposed base-colour Quote/Drop
payload are genuinely different compact terms.  The pair below therefore
cannot close through the diagonal elaboration base case. -/
theorem rhoForeignBoundaryQuotePattern_ne_payload :
    rhoForeignBoundaryQuotePattern ≠ rhoBreadthRedexA := by
  intro equality
  simp [rhoForeignBoundaryQuotePattern, rhoBreadthRedexA,
    rhoBreadthLeftProcess, rhoCutOrderWrappedDrop, rhoCutOrderBaseQuote,
    rhoCutOrderBaseDrop] at equality

/-- A raw cross-colour static/static pair closes by replaying the exact
foreign boundary occurrence and recursively closing its certified payload.

The boundary child is paired with the exposed base-colour endpoint by the
genuine diagonal constructor in the child fibre.  The enclosing pair is not
diagonal: `stoppedQuoteDropPairElaboration` transports that child alignment
through the wrapped Quote/Drop shell while retaining the stopped occurrence. -/
noncomputable def rhoForeignBoundaryQuotePairElaboration :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree [] []
      rhoForeignBoundaryQuotePattern rhoBreadthRedexA
      (.base (costBaseSortName "Name")) := by
  let leftView : rhoForeignBoundaryQuoteTree.StaticRootView .wrapped :=
    { node := rhoForeignBoundaryQuoteNode
      children := rhoForeignBoundaryQuoteChildren
      patternEq := rfl
      availableEq := rfl
      typeEq := rfl
      treeEq := rfl }
  have boundaryWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      rhoCutOrderFree
      rhoForeignBoundaryQuoteStopped.certified.typed.boundary.targetSupport
      rhoForeignBoundaryQuoteStopped.certified.typed.boundary.targetType
      rhoForeignBoundaryQuoteStopped.certified.typed.boundary.content :=
    ⟨⟨rhoForeignBoundaryQuoteStopped.certified.typed.contentTyped,
        rhoForeignBoundaryQuoteStopped.certified.typed.contentCanonicalBinderMetadata,
        rhoForeignBoundaryQuoteStopped.certified.typed.contentObjectPattern,
        rhoForeignBoundaryQuoteStopped.certified.typed.contentTyped.isWellScopedAt⟩,
      rhoForeignBoundaryQuoteStopped.certified.typed.contentReflectiveScopeSafe⟩
  let childPair := Classical.choice
    (CostCanonicalPairElaboration.nonempty_of_pattern_eq
      (kernel := rhoHereditaryNormalizationKernel) (outer := [])
      boundaryWellSorted rhoBreadthBoundaryWitnessA.content_eq)
  exact RhoCollapsingLeafExposure.stoppedQuoteDropPairElaboration
    rhoForeignBoundaryQuoteTree rhoBreadthBaseRedexATree leftView rfl
    rhoForeignBoundaryQuoteStopped (.keep (.nil [])) rfl
    rhoBreadthBoundaryWitnessA.targetSupport_eq
    (rhoBreadthBoundaryWitnessA.targetType_eq.trans
      rhoForeignWrappedNameType.symm)
    childPair

theorem rhoForeignBoundaryQuotePairElaboration_normalize_pattern_eq :
    (rhoForeignBoundaryQuotePairElaboration.leftTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoForeignBoundaryQuotePairElaboration.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  rhoForeignBoundaryQuotePairElaboration.normalize_pattern_eq

/-! ## Certified singleton-parallel boundary control

The static singleton below contains the neutral breadth process as one exact
certified boundary occurrence.  Its recursive child is deliberately reused as
the structural endpoint, so the only root-changing work left to the terminal
is occurrence selection followed by bare-parallel singleton collapse.
-/

private theorem rhoSingletonBoundaryRule_mem (index : Nat)
    (inBounds : index < 6) :
    rhoCalc.terms[index]'(by simp [rhoCalc]; omega) ∈ rhoCalc.terms :=
  List.getElem_mem _

private def rhoSingletonBoundaryParallelChoice : CostCollectionTypingChoice :=
  .bare rhoCalc.terms[3] (.base "Proc")

private theorem rhoSingletonBoundaryParallelChoice_mem :
    rhoSingletonBoundaryParallelChoice ∈
      costStaticCollectionTypingChoices rhoCIGSLT .base rhoCutOrderFree []
        .hashBag [rhoBreadthLeftPattern]
        (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
          (.base "Proc")) := by
  apply mem_costStaticCollectionTypingChoices_complete
  right
  refine ⟨rhoCalc.terms[3], .base "Proc", rfl,
    rhoSingletonBoundaryRule_mem 3 (by omega), ?_, rfl, "ps", rfl, ?_⟩
  · apply rhoCIGSLT.bareCollectionConstructorsWrapped _
      (rhoSingletonBoundaryRule_mem 3 (by omega))
    exact ⟨"ps", .hashBag, .base "Proc", rfl⟩
  · apply WellSorted.checkElementsHaveType_complete_of_objects
    · exact .cons (by
        simpa [CostStaticColor.symbols, costBaseTypeExpr] using
          rhoBreadthLeft_typed) (.nil [] _)
    · simpa only [rhoBreadthLeft, WellSorted.isObjectPatternList,
        Bool.and_eq_true, List.isEmpty_iff, decide_true, Bool.and_true] using
          rhoBreadthLeft.2.1.2.2.1

private theorem rhoSingletonBoundaryCertificate_exists :
    ∃ certificate,
      certifyCostRegionBoundary? rhoCIGSLT .base rhoCutOrderFree []
          (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
            (.base "Proc"))
          rhoBreadthLeftPattern =
        some certificate := by
  apply exists_certifyCostRegionBoundary?_eq_some
  · exact ⟨.base "Proc", decodeCostStaticTypeExpr_mapTypeExpr _ _ _⟩
  · exact rhoBreadthLeft.2

noncomputable def rhoSingletonBoundaryCertificate :
    CertifiedCostRegionBoundary rhoCIGSLT .base rhoCutOrderFree []
      (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
        (.base "Proc"))
      rhoBreadthLeftPattern :=
  Classical.choose rhoSingletonBoundaryCertificate_exists

theorem rhoSingletonBoundaryCertificate_spec :
    certifyCostRegionBoundary? rhoCIGSLT .base rhoCutOrderFree []
        (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
          (.base "Proc"))
        rhoBreadthLeftPattern =
      some rhoSingletonBoundaryCertificate :=
  Classical.choose_spec rhoSingletonBoundaryCertificate_exists

private noncomputable def rhoSingletonBoundaryElementPlan
    (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer rhoBreadthLeftPattern (.base "Proc") :=
  .boundaryApplication rhoBreadthOutputDeclared rfl
    (by rw [rhoBreadthOutputRole]; decide)
    rhoSingletonBoundaryCertificate rhoSingletonBoundaryCertificate_spec

private noncomputable def rhoSingletonBoundaryPlan :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] .hole rhoStaticNeutralSingletonPattern (.base "Proc") := by
  apply CostStaticRegionPlan.collection rhoSingletonBoundaryParallelChoice
    rhoSingletonBoundaryParallelChoice_mem
  exact .cons
    (rhoSingletonBoundaryElementPlan
      (.collection .hashBag [] .hole [] none))
    .nil

noncomputable def rhoSingletonBoundaryNode :
    CostStaticRegionNode rhoCIGSLT .base rhoCutOrderFree :=
  CostStaticRegionNode.ofPlan rhoStaticNeutralSingleton.toCore
    rhoSingletonBoundaryPlan rfl

noncomputable def rhoSingletonBoundaryChild :
    CostRegionTree rhoCIGSLT rhoCutOrderFree
      rhoSingletonBoundaryCertificate.typed.boundary.targetSupport []
      rhoSingletonBoundaryCertificate.typed.boundary.content
      rhoSingletonBoundaryCertificate.typed.boundary.targetType :=
  CostRegionTree.reindexType
    (by
      simpa [CostStaticColor.symbols, costBaseTypeExpr] using
        rhoSingletonBoundaryCertificate.targetType_eq.symm)
    (CostRegionTree.reindexPattern
      rhoSingletonBoundaryCertificate.content_eq.symm
      (CostRegionTree.reindexAvailable
        rhoSingletonBoundaryCertificate.targetSupport_eq.symm
        rhoBreadthLeftTree))

noncomputable def rhoSingletonBoundaryChildren :
    CostRegionBoundaryTrees rhoCIGSLT rhoCutOrderFree .base
      rhoSingletonBoundaryNode.finiteBoundaryTable :=
  .cons rhoSingletonBoundaryChild .nil

private theorem rhoSingletonBoundaryNode_targetBound :
    rhoSingletonBoundaryNode.targetBound = [] := rfl

private theorem rhoSingletonBoundaryNode_skeleton :
    rhoSingletonBoundaryNode.skeleton.1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.fvar (costRegionBoundaryVariableName
          rhoSingletonBoundaryCertificate.typed.boundary)] none :=
  rfl

private noncomputable def rhoSingletonBoundaryStopped :
    CostStaticPlanStopped rhoCIGSLT .base rhoCutOrderFree
      rhoBreadthLeftPattern rhoSingletonBoundaryNode.skeleton.1 where
  boundarySupport := []
  boundaryType := _
  content := rhoBreadthLeftPattern
  certified := rhoSingletonBoundaryCertificate
  certifies := rhoSingletonBoundaryCertificate_spec
  residual := .hole
  content_eq := rfl
  skeletonContext := .collection rhoReflectivePresentation.parallelCollection
    [] .hole [] none
  abstract_eq := rhoSingletonBoundaryNode_skeleton

/-- The singleton shell closes from an exact stopped occurrence and a
recursive child alignment.  Neither the semantic-atom slot nor the collapsed
canonical frame is selected by the fixture. -/
noncomputable def rhoSingletonBoundaryBridge :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      (CostRegionTree.static (outer := []) rhoSingletonBoundaryNode
        rhoSingletonBoundaryChildren)
      rhoSingletonBoundaryChild := by
  let exposure :=
    RhoCollapsingLeafExposure.stoppedParallelSingletonBoundaryElaborationAlignedSameSupport
      rhoSingletonBoundaryNode rhoSingletonBoundaryChildren
      rhoSingletonBoundaryStopped (.keep (.nil [])) rfl
      rhoSingletonBoundaryChild rhoSingletonBoundaryChild
      rhoSingletonBoundaryChild (.refl rhoSingletonBoundaryChild) rfl (by
        change
          rhoSingletonBoundaryCertificate.typed.boundary.targetSupport.length =
            rhoSingletonBoundaryNode.targetBound.length
        rw [rhoSingletonBoundaryCertificate.targetSupport_eq,
          rhoSingletonBoundaryNode_targetBound])
  exact exposure.toRootBridge

theorem rhoSingletonBoundaryBridge_normalize_pattern_eq :
    ((CostRegionTree.static (outer := []) rhoSingletonBoundaryNode
        rhoSingletonBoundaryChildren).normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoSingletonBoundaryChild.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  rhoSingletonBoundaryBridge.toTreeAlignment.normalize_pattern_eq

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
