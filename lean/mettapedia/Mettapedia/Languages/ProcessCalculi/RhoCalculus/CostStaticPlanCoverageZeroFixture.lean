import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary

/-!
# Zero-name static-plan fixture for occurrence coverage

The zero-name Quote/Drop plans and their lawful cell edge live below the
dependent context-pair and coverage constructions.  Keeping this layer in its
own module prevents later certificates from repeatedly unfolding the plan
implementation while elaborating their indices.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary

/-- Collapsed endpoint of the zero-name Quote/Drop cell. -/
def rhoCoverageZeroFvarPlan :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] .hole (.fvar "0") (.base "Name") :=
  .fvar (by
    simp [rhoCutOrderFree, FreeTypeContext.ofList, mapTypeExpr,
      CostStaticColor.symbols, costBaseStaticSymbols,
      costBaseLanguageDefSymbolMap])

/-- The zero name as a base static region. -/
def rhoCoverageZeroNameFvarPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer (.fvar "0") (.base "Name") :=
  .fvar (by
    simp [rhoCutOrderFree, FreeTypeContext.ofList, mapTypeExpr,
      CostStaticColor.symbols, costBaseStaticSymbols,
      costBaseLanguageDefSymbolMap])

/-- Base drop cell over the zero name. -/
def rhoCoverageZeroDropPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer (rhoCutOrderBaseDrop (.fvar "0")) (.base "Proc") := by
  apply CostStaticRegionPlan.application rhoBreadthBaseDropDeclared rfl
    rhoBreadthBaseDropRole rhoBreadthBaseDropPreimage
  · exact rhoBreadthBaseDrop_notBare
  · exact .cons (by trivial) rfl
      (rhoCoverageZeroNameFvarPlan
        (outer.comp
          (.apply (costBaseConstructorName "PDrop") [] .hole [])))
      .nil

/-- The zero-name Quote/Drop region. -/
def rhoCoverageZeroRedexPlan :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] .hole rhoCutOrderRedex (.base "Name") := by
  apply CostStaticRegionPlan.application rhoBreadthBaseQuoteDeclared rfl
    rhoBreadthBaseQuoteRole rhoBreadthBaseQuotePreimage
  · exact rhoBreadthBaseQuote_notBare
  · exact .cons (by trivial) rfl
      (rhoCoverageZeroDropPlan
        (OneHoleContext.hole.comp
          (.apply (costBaseConstructorName "NQuote") [] .hole [])))
      .nil

/-- The zero-name collapse as a source-language reflective occurrence
between the two decoration skeletons. -/
def rhoCoverageZeroCollapseWitness :
    ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.reflection.1 defaultBasePremises
      rhoCIGSLT.theory.presentation.presentation.language
      rhoCoverageZeroRedexPlan.decoration.abstractPattern
      rhoCoverageZeroFvarPlan.decoration.abstractPattern := by
  refine ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness.reflective .hole
    ⟨rhoReflectivePresentation.toReflectivePresentationDecl,
      rhoPairSourceReflectiveDecl_mem⟩ ?_
  have leftEq : rhoCoverageZeroRedexPlan.decoration.abstractPattern =
      .apply "NQuote" [.apply "PDrop"
        [.fvar (costRegionSourceVariableName "0")]] := by
    unfold rhoCoverageZeroRedexPlan rhoCoverageZeroDropPlan
      rhoCoverageZeroNameFvarPlan
    simp [CostStaticRegionPlan.decoration,
      CostStaticArgumentPlan.decorations,
      CostStaticPlanDecoration.abstractPattern,
      CostStaticPlanDecorationNode.abstractPattern,
      rhoBreadthBaseQuotePreimage, rhoBreadthBaseDropPreimage,
      costStaticConstructorPreimage, rhoBreadthBaseQuoteDeclared,
      rhoBreadthBaseDropDeclared, rhoCalc]
  have rightEq : rhoCoverageZeroFvarPlan.decoration.abstractPattern =
      .fvar (costRegionSourceVariableName "0") := by
    simp [rhoCoverageZeroFvarPlan, CostStaticRegionPlan.decoration,
      CostStaticPlanDecoration.abstractPattern,
      CostStaticPlanDecorationNode.abstractPattern]
  rw [leftEq, rightEq]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    rhoReflectivePresentation]

/-- The zero-name collapse as a lawful cell-level edge. -/
def rhoCoverageZeroCollapseEdge :
    CostStaticPlanEdge rhoCIGSLT rhoCoverageZeroRedexPlan.decoration
      rhoCoverageZeroFvarPlan.decoration [] [] where
  sameFiber := ⟨rfl, rfl, rfl, rfl, rfl⟩
  generatorWitness := rhoCoverageZeroCollapseWitness
  sourceBoundaryInventory := rfl
  targetBoundaryInventory := rfl
  boundaryOrigins := CostBoundaryFiberMap.identity []
  choiceOrigins :=
    { origin := fun _index => none
      preservesFiber := fun _target _source impossible => nomatch impossible }
  introducedChoice := fun targetIndex _origin =>
    ((show rhoCoverageZeroFvarPlan.decoration.choiceOccurrences = []
      from rfl) ▸ targetIndex).elim0
  sourceContextChoiceCovered := fun _sourceIndex notInRedex =>
    absurd ⟨_, rfl⟩ notInRedex
  boundaryChoiceCoherent := fun targetIndex => targetIndex.elim0

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary
