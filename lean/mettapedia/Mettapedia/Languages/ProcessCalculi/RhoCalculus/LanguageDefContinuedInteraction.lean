import Mettapedia.GSLT.LanguageDef.ContinuedCategory
import Mettapedia.GSLT.LanguageDef.CanonicalConstructorSupport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSupport

/-!
# Continued-interaction data derived from `rhoCalc`

This file supplies rho's declaration-level wrappability witness.  The
contractum is still the right-hand side of the authored `Comm` rule.  Every
constructor other than the input and output introductions receives a wrapped
copy; the contractum uses the parallel and quotation copies.  Consequently
the transformed contractum has the wrapped-term sort without exposing a new
unguarded communication redex.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSupport

private def rhoContinuationParallelConstructor :
    AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoParallelConstructor.1, by
    exact rhoParallelConstructor.2⟩

private def rhoContinuationQuoteConstructor :
    AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoQuoteConstructor.1, by
    exact rhoQuoteConstructor.2⟩

private def rhoContinuationDropConstructor :
    AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[1], by
    change rhoCalc.terms[1] ∈ rhoCalc.terms
    exact List.getElem_mem (by simp [rhoCalc])⟩

private def rhoContinuationUnitConstructor :
    AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[0], by
    change rhoCalc.terms[0] ∈ rhoCalc.terms
    exact List.getElem_mem (by simp [rhoCalc])⟩

/-- Rho's COMM contractum is covered by the hereditary continuation closure
derived from its ordered interaction cut. -/
def rhoContinuationRetyping : ContinuationRetypingPlan rhoInteractionCut where
  residualCovered := by
    change rhoContinuationParallelConstructor ∈
      continuationConstructors rhoInteractionCut
    apply (mem_continuationConstructors_iff rhoInteractionCut
      rhoContinuationParallelConstructor).2
    constructor <;> decide

/-- Rho's authored COMM contractum is well-sorted on wrapped continuations.
This is the declaration-level wrappability obligation of the continued
interaction structure. -/
theorem rhoContinuationRetyping_wrappable :
    rhoContinuationRetyping.Wrappable := by
  unfold ContinuationRetypingPlan.Wrappable
  change HasType rhoContinuationRetyping.generatedLanguage
    rhoContinuationRetyping.generatedFreeContext []
    (.collection .hashBag
      [.subst (.fvar "p")
        (.apply (costWrappedConstructorName "NQuote") [.fvar "q"])]
      (some "rest"))
    (.base costWrappedSortName)
  apply HasType.collectionConstructor
      (rule := costWrappedConstructor
        (theory := rhoIGSLT) rhoParallelConstructor.1)
      (parameterName := "ps")
      (elementType := .base costWrappedSortName)
  · have selected : rhoContinuationParallelConstructor ∈
        rhoContinuationRetyping.wrappedConstructors :=
      (rhoContinuationRetyping.mem_wrappedConstructors_iff
        rhoContinuationParallelConstructor).2 (by
          constructor <;> decide)
    simpa [rhoContinuationParallelConstructor] using
      rhoContinuationRetyping.costWrappedConstructor_mem_generated
        rhoContinuationParallelConstructor selected
  · rfl
  · apply ElementsHaveType.cons
    · apply HasType.subst
        (domain := .base (costBaseSortName "Name"))
        (codomain := .base costWrappedSortName)
      · apply HasType.fvar
        rfl
      · apply HasType.constructor
          (rule := costWrappedConstructor
            (theory := rhoIGSLT) rhoQuoteConstructor.1)
        · have selected : rhoContinuationQuoteConstructor ∈
              rhoContinuationRetyping.wrappedConstructors :=
            (rhoContinuationRetyping.mem_wrappedConstructors_iff
              rhoContinuationQuoteConstructor).2 (by
                constructor <;> decide)
          simpa [rhoContinuationQuoteConstructor] using
            rhoContinuationRetyping.costWrappedConstructor_mem_generated
              rhoContinuationQuoteConstructor selected
        · simp [WellSorted.UsesBareCollection, costWrappedConstructor,
            mapParameterType, costWrappedTypeExpr, rhoIGSLT,
            rhoInteractivePresentation, rhoQuoteConstructor, rhoCalc,
            TypeDecl.plain, TypeExpr.proc, TypeExpr.baseType]
        · apply ArgumentsHaveTypes.cons
          · simp [MatchesParameterRepresentation, mapParameterType]
          · rfl
          · apply HasType.fvar
            rfl
          · exact .nil
    · exact .nil _ _

@[simp]
theorem rho_costBaseParallelConstructor_params :
    (costBaseConstructor rhoInteractionCut rhoCalc.terms[3]).params =
      [.simple "ps"
        (.collection .hashBag (.base (costBaseSortName "Proc")))] := by
  simp [costBaseConstructor, costBaseParameter, isSelectedContinuation,
    rhoCalc, mapParameterType, costBaseTypeExpr,
    rhoInteractionCut_program_constructor_value,
    rhoInteractionCut_environment_constructor_value,
    rhoInteractionCut_program_continuation_index,
    rhoInteractionCut_environment_continuation_index,
    TypeExpr.proc, TypeExpr.baseType, TypeExpr.bag]

@[simp]
theorem rho_costWrappedParallelConstructor_params :
    (costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[3]).params =
      [.simple "ps"
        (.collection .hashBag (.base costWrappedSortName))] := by
  simp [costWrappedConstructor, rhoCalc, mapParameterType,
    costWrappedTypeExpr, rhoIGSLT, rhoInteractivePresentation,
    TypeDecl.plain, TypeExpr.proc, TypeExpr.baseType, TypeExpr.bag]

/-- The same raw empty-bag representation inhabits both generated process
fibers.  Its intended canonical unit is therefore determined by the derived
sort, not by the `Pattern` node alone. -/
theorem rhoCost_emptyParallel_has_base_and_wrapped_sort :
    HasSort rhoContinuationRetyping.generatedLanguage
        FreeTypeContext.empty [] (.collection .hashBag [] none)
        (costBaseSortName "Proc") ∧
      HasSort rhoContinuationRetyping.generatedLanguage
        FreeTypeContext.empty [] (.collection .hashBag [] none)
        costWrappedSortName := by
  constructor
  · apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base (costBaseSortName "Proc"))
    · simpa [rhoContinuationParallelConstructor, rhoParallelConstructor] using
        rhoContinuationRetyping.costBaseConstructor_mem_generated
          rhoContinuationParallelConstructor.1
          rhoContinuationParallelConstructor.2
    · exact rho_costBaseParallelConstructor_params
    · exact .nil [] _
  · apply HasType.collectionConstructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base costWrappedSortName)
    · have wrapped : rhoContinuationParallelConstructor ∈
          rhoContinuationRetyping.wrappedConstructors :=
        (rhoContinuationRetyping.mem_wrappedConstructors_iff
          rhoContinuationParallelConstructor).2 (by
            constructor <;> decide)
      simpa [rhoContinuationParallelConstructor, rhoParallelConstructor] using
        rhoContinuationRetyping.costWrappedConstructor_mem_generated
          rhoContinuationParallelConstructor wrapped
    · exact rho_costWrappedParallelConstructor_params
    · exact .nil [] _

/-- No canonicalizer on raw patterns alone can choose the two distinct
generated units required by the base and wrapped process fibers.  The sort
index retained by `OpenTerm` is therefore semantic data for generated Cost,
not an implementation convenience. -/
theorem no_raw_normalizer_selects_both_rhoCost_units
    (normalize : Pattern → Pattern)
    (baseUnit :
      normalize (.collection .hashBag [] none) =
        .apply (costBaseConstructorName "PZero") [])
    (wrappedUnit :
      normalize (.collection .hashBag [] none) =
        .apply (costWrappedConstructorName "PZero") []) :
    False := by
  have unitsEqual :
      Pattern.apply (costBaseConstructorName "PZero") [] =
        Pattern.apply (costWrappedConstructorName "PZero") [] :=
    baseUnit.symm.trans wrappedUnit
  have labelsEqual :
      costBaseConstructorName "PZero" =
        costWrappedConstructorName "PZero" := by
    injection unitsEqual
  exact costBaseConstructorName_ne_wrapped "PZero" "PZero" labelsEqual

@[simp]
theorem rho_costBaseInputConstructor_params :
    (costBaseConstructor rhoInteractionCut rhoCalc.terms[5]).params =
      [.simple "n" (.base (costBaseSortName "Name")),
        .abstraction "p"
          (.arrow (.base (costBaseSortName "Name"))
            (.base costWrappedSortName))] := by
  simp [costBaseConstructor, costBaseParameter, isSelectedContinuation,
    rhoCalc, mapParameterType, costBaseTypeExpr, costWrappedTypeExpr,
    rhoInteractionCut_program_constructor_value,
    rhoInteractionCut_environment_constructor_value,
    rhoInteractionCut_program_continuation_index,
    rhoInteractionCut_environment_continuation_index,
    rhoIGSLT, rhoInteractivePresentation, TypeDecl.plain,
    TypeExpr.name, TypeExpr.proc, TypeExpr.funType, TypeExpr.baseType]

@[simp]
theorem rho_costBaseOutputConstructor_params :
    (costBaseConstructor rhoInteractionCut rhoCalc.terms[4]).params =
      [.simple "n" (.base (costBaseSortName "Name")),
        .simple "q" (.base costWrappedSortName)] := by
  simp [costBaseConstructor, costBaseParameter, isSelectedContinuation,
    rhoCalc, mapParameterType, costBaseTypeExpr, costWrappedTypeExpr,
    rhoInteractionCut_program_constructor_value,
    rhoInteractionCut_environment_constructor_value,
    rhoInteractionCut_program_continuation_index,
    rhoInteractionCut_environment_continuation_index,
    rhoIGSLT, rhoInteractivePresentation, TypeDecl.plain,
    TypeExpr.name, TypeExpr.proc, TypeExpr.baseType]

@[simp]
theorem rho_costBaseQuoteConstructor_params :
    (costBaseConstructor rhoInteractionCut rhoCalc.terms[2]).params =
      [.simple "p" (.base (costBaseSortName "Proc"))] := by
  simp [costBaseConstructor, costBaseParameter, isSelectedContinuation,
    rhoCalc, mapParameterType, costBaseTypeExpr,
    rhoInteractionCut_program_constructor_value,
    rhoInteractionCut_environment_constructor_value,
    TypeExpr.proc, TypeExpr.baseType]

@[simp]
theorem rho_costBaseDropConstructor_params :
    (costBaseConstructor rhoInteractionCut rhoCalc.terms[1]).params =
      [.simple "n" (.base (costBaseSortName "Name"))] := by
  simp [costBaseConstructor, costBaseParameter, isSelectedContinuation,
    rhoCalc, mapParameterType, costBaseTypeExpr,
    rhoInteractionCut_program_constructor_value,
    rhoInteractionCut_environment_constructor_value,
    TypeExpr.name, TypeExpr.baseType]

@[simp]
theorem rho_costWrappedQuoteConstructor_params :
    (costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[2]).params =
      [.simple "p" (.base costWrappedSortName)] := by
  simp [costWrappedConstructor, rhoCalc, mapParameterType,
    costWrappedTypeExpr, rhoIGSLT, rhoInteractivePresentation,
    TypeDecl.plain, TypeExpr.proc, TypeExpr.baseType]

@[simp]
theorem rho_costWrappedDropConstructor_params :
    (costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1]).params =
      [.simple "n" (.base (costBaseSortName "Name"))] := by
  simp [costWrappedConstructor, rhoCalc, mapParameterType,
    costWrappedTypeExpr, rhoIGSLT, rhoInteractivePresentation,
    TypeDecl.plain, TypeExpr.name, TypeExpr.baseType]

/-- Rho's authored COMM redex remains well-sorted after the input and output
continuation positions are moved to the wrapped fiber. -/
theorem rhoContinuationRetyping_redexRetypable :
    rhoContinuationRetyping.RedexRetypable := by
  unfold ContinuationRetypingPlan.RedexRetypable
  change HasType rhoContinuationRetyping.generatedLanguage
    rhoContinuationRetyping.generatedFreeContext []
    (mapPattern costBasePresentationSymbols rhoCommRewrite.left)
    (.base (costBaseSortName "Proc"))
  simp only [rhoCommRewrite, mapPattern, costBasePresentationSymbols]
  apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base (costBaseSortName "Proc"))
  · simpa [rhoParallelConstructor] using
      rhoContinuationRetyping.costBaseConstructor_mem_generated
        rhoParallelConstructor.1 rhoParallelConstructor.2
  · exact rho_costBaseParallelConstructor_params
  · apply ElementsHaveType.cons
    · apply HasType.constructor
        (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[5])
      · simpa only [rhoInteractionCut_program_constructor_value] using
          rhoContinuationRetyping.costBaseConstructor_mem_generated
            rhoInteractionCut.program.constructor.1
            rhoInteractionCut.program.constructor.2
      · simp [WellSorted.UsesBareCollection,
          rho_costBaseInputConstructor_params]
      · rw [rho_costBaseInputConstructor_params]
        apply ArgumentsHaveTypes.cons
        · trivial
        · rfl
        · exact HasType.fvar rfl
        · apply ArgumentsHaveTypes.cons
          · trivial
          · rfl
          · apply HasType.lambda
            exact HasType.fvar rfl
          · exact .nil
    · apply ElementsHaveType.cons
      · apply HasType.constructor
          (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[4])
        · simpa only [rhoInteractionCut_environment_constructor_value] using
            rhoContinuationRetyping.costBaseConstructor_mem_generated
              rhoInteractionCut.environment.constructor.1
              rhoInteractionCut.environment.constructor.2
        · simp [WellSorted.UsesBareCollection,
            rho_costBaseOutputConstructor_params]
        · rw [rho_costBaseOutputConstructor_params]
          apply ArgumentsHaveTypes.cons
          · trivial
          · rfl
          · exact HasType.fvar rfl
          · apply ArgumentsHaveTypes.cons
            · trivial
            · rfl
            · exact HasType.fvar rfl
            · exact .nil
      · exact .nil _ _

/-- Rho's sole static equation transports to both the unchanged base copy
and the hereditary wrapped copy.  Its constructors are residual rather than
interaction principals, so both images remain sorted. -/
theorem rhoContinuationRetyping_equationsRetypable :
    EquationsRetypable rhoContinuationRetyping := by
  intro equation membership
  change equation ∈ rhoCalc.equations at membership
  simp only [rhoCalc, List.mem_singleton] at membership
  subst equation
  refine
    { premiseFree := rfl
      leftInstantiationStable := by
        simp [schemaInstantiationStable,
          schemaHasNoCollectionRest, schemaListHasNoCollectionRest,
          Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList]
      rightInstantiationStable := by
        simp [schemaInstantiationStable,
          schemaHasNoCollectionRest,
          Pattern.hasCanonicalBinderMetadata]
      leftMatchCorrect := rfl
      rightMatchCorrect := rfl
      baseWellSorted := ?_
      wrappedWellSorted := ?_ }
  · refine ⟨.base (costBaseSortName "Name"), ?_, ?_⟩
    · simp only [costBaseEquation, Mettapedia.GSLT.LanguageDef.mapEquation,
        mapTypeContext,
        costBaseStaticSymbols, costBasePresentationSymbols, mapPattern,
        List.map]
      change HasType rhoContinuationRetyping.generatedLanguage
        (FreeTypeContext.ofList
          [("N", .base (costBaseSortName "Name"))]) []
        (.apply (costBaseConstructorName "NQuote")
          [.apply (costBaseConstructorName "PDrop") [.fvar "N"]])
        (.base (costBaseSortName "Name"))
      apply HasType.constructor
          (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[2])
      · apply rhoContinuationRetyping.costBaseConstructor_mem_generated
        change rhoCalc.terms[2] ∈ rhoCalc.terms
        exact List.getElem_mem (by simp [rhoCalc])
      · rw [usesBareCollection_costBaseConstructor_iff]
        simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
          TypeExpr.baseType]
      · rw [rho_costBaseQuoteConstructor_params]
        apply ArgumentsHaveTypes.cons
        · trivial
        · rfl
        · apply HasType.constructor
            (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[1])
          · apply rhoContinuationRetyping.costBaseConstructor_mem_generated
            change rhoCalc.terms[1] ∈ rhoCalc.terms
            exact List.getElem_mem (by simp [rhoCalc])
          · rw [usesBareCollection_costBaseConstructor_iff]
            simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
              TypeExpr.baseType]
          · rw [rho_costBaseDropConstructor_params]
            apply ArgumentsHaveTypes.cons
            · trivial
            · rfl
            · exact HasType.fvar rfl
            · exact .nil
        · exact .nil
    · simp only [costBaseEquation, Mettapedia.GSLT.LanguageDef.mapEquation,
        mapTypeContext,
        costBaseStaticSymbols, costBasePresentationSymbols, mapPattern,
        List.map]
      change HasType rhoContinuationRetyping.generatedLanguage
        (FreeTypeContext.ofList
          [("N", .base (costBaseSortName "Name"))]) []
        (.fvar "N") (.base (costBaseSortName "Name"))
      apply HasType.fvar
      simp [FreeTypeContext.ofList]

  · refine ⟨.base (costBaseSortName "Name"), ?_, ?_⟩
    · simp only [costWrappedEquation,
        Mettapedia.GSLT.LanguageDef.mapEquation, mapTypeContext,
        costWrappedStaticSymbols, mapTypeExpr,
        mapPattern, List.map, rhoIGSLT, rhoInteractivePresentation,
        TypeExpr.name, TypeExpr.baseType]
      change HasType rhoContinuationRetyping.generatedLanguage
        (FreeTypeContext.ofList
          [("N", .base (costBaseSortName "Name"))]) []
        (.apply (costWrappedConstructorName "NQuote")
          [.apply (costWrappedConstructorName "PDrop") [.fvar "N"]])
        (.base (costBaseSortName "Name"))
      apply HasType.constructor
          (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[2])
      · have selected : rhoContinuationQuoteConstructor ∈
            rhoContinuationRetyping.wrappedConstructors :=
          (rhoContinuationRetyping.mem_wrappedConstructors_iff
            rhoContinuationQuoteConstructor).2 (by
              constructor <;> decide)
        simpa [rhoContinuationQuoteConstructor, rhoQuoteConstructor] using
          rhoContinuationRetyping.costWrappedConstructor_mem_generated
            rhoContinuationQuoteConstructor selected
      · rw [usesBareCollection_costWrappedConstructor_iff]
        simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
          TypeExpr.baseType]
      · rw [rho_costWrappedQuoteConstructor_params]
        apply ArgumentsHaveTypes.cons
        · trivial
        · rfl
        · apply HasType.constructor
            (rule := costWrappedConstructor
              (theory := rhoIGSLT) rhoCalc.terms[1])
          · have selected : rhoContinuationDropConstructor ∈
                rhoContinuationRetyping.wrappedConstructors :=
              (rhoContinuationRetyping.mem_wrappedConstructors_iff
                rhoContinuationDropConstructor).2 (by
                  constructor <;> decide)
            simpa [rhoContinuationDropConstructor] using
              rhoContinuationRetyping.costWrappedConstructor_mem_generated
                rhoContinuationDropConstructor selected
          · rw [usesBareCollection_costWrappedConstructor_iff]
            simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
              TypeExpr.baseType]
          · rw [rho_costWrappedDropConstructor_params]
            apply ArgumentsHaveTypes.cons
            · trivial
            · rfl
            · exact HasType.fvar rfl
            · exact .nil
        · exact .nil
    · simp only [costWrappedEquation,
        Mettapedia.GSLT.LanguageDef.mapEquation, mapTypeContext,
        costWrappedStaticSymbols, mapTypeExpr,
        mapPattern, List.map, rhoIGSLT, rhoInteractivePresentation,
        TypeExpr.name, TypeExpr.baseType]
      change HasType rhoContinuationRetyping.generatedLanguage
        (FreeTypeContext.ofList
          [("N", .base (costBaseSortName "Name"))]) []
        (.fvar "N") (.base (costBaseSortName "Name"))
      apply HasType.fvar
      simp [FreeTypeContext.ofList]

/-- Rho's reflective quote, drop, and parallel-unit constructors are all
residual constructors, never the input/output interaction principals. -/
theorem rhoContinuationRetyping_reflectivePresentationsRetypable :
    ReflectivePresentationsRetypable rhoContinuationRetyping
      rhoReflectionProfile := by
  intro declaration membership
  change declaration ∈ rhoReflectionProfile.presentations at membership
  simp only [rhoReflectionProfile, List.mem_singleton] at membership
  subst declaration
  constructor
  · apply LanguageDef.validateReflectivePresentation_eq_nil_of_unique
      (quote := costBaseConstructor rhoInteractionCut rhoCalc.terms[2])
      (drop := costBaseConstructor rhoInteractionCut rhoCalc.terms[1])
      (unit := costBaseConstructor rhoInteractionCut rhoCalc.terms[0])
      (equation := costBaseEquation rhoCalc.equations[0])
      (quoteParameter := "p") (dropParameter := "n")
      (equationVariable := "N")
    · apply rhoContinuationRetyping.costBaseSortName_mem_generated
      simp [rhoIGSLT, rhoInteractivePresentation, rhoValidatedLanguageDef,
        rhoCalc, rhoReflectivePresentation, LanguageDef.typeNames,
        TypeDecl.plain]
    · apply rhoContinuationRetyping.costBaseSortName_mem_generated
      simp [rhoIGSLT, rhoInteractivePresentation, rhoValidatedLanguageDef,
        rhoCalc, rhoReflectivePresentation, LanguageDef.typeNames,
        TypeDecl.plain]
    · intro equality
      have sourceEquality : "Proc" = "Name" :=
        costBaseSortName_injective equality
      simp at sourceEquality
    · simpa [reflectiveRetypingLanguage,
        costBaseReflectivePresentationDecl, costBaseStaticSymbols,
        costBaseStaticReflectiveSymbols,
        costBasePresentationSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        rhoReflectivePresentation, rhoCalc] using
        rhoContinuationRetyping.costBaseConstructor_filter_generated
          rhoCalc.terms[2] rhoQuoteConstructor.2
    · rfl
    · exact rho_costBaseQuoteConstructor_params
    · simpa [reflectiveRetypingLanguage,
        costBaseReflectivePresentationDecl, costBaseStaticSymbols,
        costBaseStaticReflectiveSymbols,
        costBasePresentationSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        rhoReflectivePresentation, rhoCalc] using
        rhoContinuationRetyping.costBaseConstructor_filter_generated
          rhoCalc.terms[1] rhoContinuationDropConstructor.2
    · rfl
    · exact rho_costBaseDropConstructor_params
    · simpa [reflectiveRetypingLanguage,
        costBaseReflectivePresentationDecl, costBaseStaticSymbols,
        costBaseStaticReflectiveSymbols,
        costBasePresentationSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        rhoReflectivePresentation, rhoCalc] using
        rhoContinuationRetyping.costBaseConstructor_filter_generated
          rhoCalc.terms[0] rhoContinuationUnitConstructor.2
    · rfl
    · rfl
    · simp [reflectiveRetypingLanguage, rhoIGSLT,
        rhoInteractivePresentation, rhoValidatedLanguageDef, rhoCalc,
        rhoReflectivePresentation, costBaseReflectivePresentationDecl,
        costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
        costBasePresentationSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        costBaseEquation, costWrappedEquation,
        Mettapedia.GSLT.LanguageDef.mapEquation, costBaseStaticSymbols,
        costWrappedStaticSymbols, mapTypeContext, mapPattern]
    · left
      constructor <;>
        simp [costBaseEquation, Mettapedia.GSLT.LanguageDef.mapEquation,
          costBaseStaticSymbols, costBasePresentationSymbols, mapPattern,
          rhoCalc, rhoReflectivePresentation,
          costBaseReflectivePresentationDecl,
          costBaseStaticReflectiveSymbols,
          Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation]
  · apply LanguageDef.validateReflectivePresentation_eq_nil_of_unique
      (quote := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[2])
      (drop := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1])
      (unit := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[0])
      (equation := costWrappedEquation rhoIGSLT rhoCalc.equations[0])
      (quoteParameter := "p") (dropParameter := "n")
      (equationVariable := "N")
    · exact rhoContinuationRetyping.costWrappedSortName_mem_generated
    · apply rhoContinuationRetyping.costBaseSortName_mem_generated
      simp [rhoIGSLT, rhoInteractivePresentation, rhoValidatedLanguageDef,
        rhoCalc, rhoReflectivePresentation, LanguageDef.typeNames,
        TypeDecl.plain]
    · exact (costBaseSortName_ne_wrapped "Name").symm
    · have selected : rhoContinuationQuoteConstructor ∈
          rhoContinuationRetyping.wrappedConstructors :=
        (rhoContinuationRetyping.mem_wrappedConstructors_iff
          rhoContinuationQuoteConstructor).2 (by
            constructor <;> decide)
      simpa [reflectiveRetypingLanguage,
        costWrappedReflectivePresentationDecl, costWrappedStaticSymbols,
        costWrappedStaticReflectiveSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        rhoReflectivePresentation, rhoContinuationQuoteConstructor,
        rhoQuoteConstructor, costWrappedConstructor, rhoCalc] using
        rhoContinuationRetyping.costWrappedConstructor_filter_generated
          rhoContinuationQuoteConstructor selected
    · simp [costWrappedConstructor, rhoIGSLT, rhoInteractivePresentation,
        rhoValidatedLanguageDef, rhoCalc,
        costWrappedReflectivePresentationDecl,
        costWrappedStaticReflectiveSymbols, costWrappedStaticSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        rhoReflectivePresentation]
    · exact rho_costWrappedQuoteConstructor_params
    · have selected : rhoContinuationDropConstructor ∈
          rhoContinuationRetyping.wrappedConstructors :=
        (rhoContinuationRetyping.mem_wrappedConstructors_iff
          rhoContinuationDropConstructor).2 (by
            constructor <;> decide)
      simpa [reflectiveRetypingLanguage,
        costWrappedReflectivePresentationDecl, costWrappedStaticSymbols,
        costWrappedStaticReflectiveSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        rhoReflectivePresentation, rhoContinuationDropConstructor,
        costWrappedConstructor, rhoCalc] using
        rhoContinuationRetyping.costWrappedConstructor_filter_generated
          rhoContinuationDropConstructor selected
    · simp [costWrappedConstructor, rhoIGSLT, rhoInteractivePresentation,
        rhoValidatedLanguageDef, rhoCalc,
        costWrappedReflectivePresentationDecl,
        costWrappedStaticReflectiveSymbols, costWrappedStaticSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        rhoReflectivePresentation]
    · exact rho_costWrappedDropConstructor_params
    · have selected : rhoContinuationUnitConstructor ∈
          rhoContinuationRetyping.wrappedConstructors :=
        (rhoContinuationRetyping.mem_wrappedConstructors_iff
          rhoContinuationUnitConstructor).2 (by
            constructor <;> decide)
      simpa [reflectiveRetypingLanguage,
        costWrappedReflectivePresentationDecl, costWrappedStaticSymbols,
        costWrappedStaticReflectiveSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        rhoReflectivePresentation, rhoContinuationUnitConstructor,
        costWrappedConstructor, rhoCalc] using
        rhoContinuationRetyping.costWrappedConstructor_filter_generated
          rhoContinuationUnitConstructor selected
    · simp [costWrappedConstructor, rhoIGSLT, rhoInteractivePresentation,
        rhoValidatedLanguageDef, rhoCalc,
        costWrappedReflectivePresentationDecl,
        costWrappedStaticReflectiveSymbols, costWrappedStaticSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        rhoReflectivePresentation]
    · rfl
    · simp [reflectiveRetypingLanguage, rhoIGSLT,
        rhoInteractivePresentation, rhoValidatedLanguageDef, rhoCalc,
        rhoReflectivePresentation, costWrappedReflectivePresentationDecl,
        costWrappedStaticReflectiveSymbols,
        Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation,
        costBaseEquation, costWrappedEquation,
        Mettapedia.GSLT.LanguageDef.mapEquation, costBaseStaticSymbols,
        costWrappedStaticSymbols, mapTypeContext, mapPattern]
      rfl
    · left
      constructor <;>
        simp [costWrappedEquation, Mettapedia.GSLT.LanguageDef.mapEquation,
          costWrappedStaticSymbols, mapPattern, rhoCalc, rhoIGSLT,
          rhoInteractivePresentation, rhoValidatedLanguageDef,
          rhoReflectivePresentation, costWrappedReflectivePresentationDecl,
          costWrappedStaticReflectiveSymbols,
          Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation]

/-- Rho's reflective quote, drop, and parallel unit are all genuine
non-principal constructors selected by the interaction cut. -/
theorem rhoReflectiveConstructorsAllowed :
    ReflectiveConstructorsAllowed
      (· ∈ rhoContinuationRetyping.wrappedLabels)
      rhoReflectivePresentation := by
  constructor
  · have selected : rhoContinuationQuoteConstructor ∈
        rhoContinuationRetyping.wrappedConstructors :=
      (rhoContinuationRetyping.mem_wrappedConstructors_iff
        rhoContinuationQuoteConstructor).2 (by
          constructor <;> decide)
    simpa [rhoContinuationQuoteConstructor, rhoQuoteConstructor, rhoCalc,
      rhoReflectivePresentation] using
      (rhoContinuationRetyping.mem_wrappedLabels_iff
        rhoContinuationQuoteConstructor).2 selected
  · have selected : rhoContinuationDropConstructor ∈
        rhoContinuationRetyping.wrappedConstructors :=
      (rhoContinuationRetyping.mem_wrappedConstructors_iff
        rhoContinuationDropConstructor).2 (by
          constructor <;> decide)
    simpa [rhoContinuationDropConstructor, rhoCalc,
      rhoReflectivePresentation] using
      (rhoContinuationRetyping.mem_wrappedLabels_iff
        rhoContinuationDropConstructor).2 selected
  · have selected : rhoContinuationUnitConstructor ∈
        rhoContinuationRetyping.wrappedConstructors :=
      (rhoContinuationRetyping.mem_wrappedConstructors_iff
        rhoContinuationUnitConstructor).2 (by
          constructor <;> decide)
    simpa [rhoContinuationUnitConstructor, rhoCalc,
      rhoReflectivePresentation] using
      (rhoContinuationRetyping.mem_wrappedLabels_iff
        rhoContinuationUnitConstructor).2 selected

/-- Rho's declaration-compiled open canonicalizer preserves the exact
non-principal constructor fragment selected by its interaction cut. -/
theorem rhoContextualOpenSection_preservesWrappedConstructors :
    rhoContextualOpenSection.PreservesConstructors
      (· ∈ rhoContinuationRetyping.wrappedLabels) := by
  apply ComputableReflectiveFiberContextualSection.preservesConstructors_reflective
    rhoContextualOpenSection rhoReflectivePresentation
  · intro free bound sort term
    change Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
        term.1 =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        rhoReflectivePresentation term.1
    exact (CanonicalMatch.derivedCanonicalize_eq term.1).symm
  · exact rhoReflectiveConstructorsAllowed

/-- Rho's sole bare collection constructor is parallel composition, which
belongs to the cut-derived non-principal fragment. -/
theorem rhoBareCollectionConstructorsWrapped :
    ∀ rule ∈ rhoCalc.terms,
      WellSorted.UsesBareCollection rule →
        rule.label ∈ rhoContinuationRetyping.wrappedLabels := by
  intro rule membership bare
  change rule ∈ [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2],
    rhoCalc.terms[3], rhoCalc.terms[4], rhoCalc.terms[5]] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with first | second | third | fourth | fifth | sixth
  · subst rule
    simp [rhoCalc, WellSorted.UsesBareCollection, TypeExpr.name,
      TypeExpr.proc, TypeExpr.baseType] at bare
  · subst rule
    simp [rhoCalc, WellSorted.UsesBareCollection, TypeExpr.name,
      TypeExpr.proc, TypeExpr.baseType] at bare
  · subst rule
    simp [rhoCalc, WellSorted.UsesBareCollection, TypeExpr.name,
      TypeExpr.proc, TypeExpr.baseType] at bare
  · subst rule
    have selected : rhoContinuationParallelConstructor ∈
        rhoContinuationRetyping.wrappedConstructors :=
      (rhoContinuationRetyping.mem_wrappedConstructors_iff
        rhoContinuationParallelConstructor).2 (by
          constructor <;> decide)
    simpa [rhoContinuationParallelConstructor, rhoParallelConstructor,
      rhoCalc] using
      (rhoContinuationRetyping.mem_wrappedLabels_iff
        rhoContinuationParallelConstructor).2 selected
  · subst rule
    simp [rhoCalc, WellSorted.UsesBareCollection, TypeExpr.name,
      TypeExpr.proc, TypeExpr.baseType] at bare
  · subst rule
    simp [rhoCalc, WellSorted.UsesBareCollection, TypeExpr.name,
      TypeExpr.proc, TypeExpr.baseType] at bare

/-- Rho's declaration-compiled open canonicalizer preserves the exact typed
non-principal constructor fragment selected by its interaction cut. -/
theorem rhoContextualOpenSection_preservesWrappedConstructorTyping :
    rhoContextualOpenSection.PreservesTypedConstructors
      (· ∈ rhoContinuationRetyping.wrappedLabels) := by
  apply ComputableReflectiveFiberContextualSection.preservesTypedConstructors_reflective
    rhoContextualOpenSection rhoReflectivePresentation
  · intro free bound sort term
    change Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
        term.1 =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        rhoReflectivePresentation term.1
    exact (CanonicalMatch.derivedCanonicalize_eq term.1).symm
  · exact rhoReflectiveConstructorsAllowed
  · exact rhoBareCollectionConstructorsWrapped

/-- Pure rho, derived from the sole `rhoCalc` definition, is a continued
interactive GSLT. -/
def rhoCIGSLT : CIGSLT where
  theory := rhoIGSLT
  reflection := rhoCalcValidatedReflective.admittedReflection
  cut := rhoInteractionCut
  openCanonical := rhoContextualOpenSection
  continuationRetyping := rhoContinuationRetyping
  bareCollectionConstructorsWrapped :=
    rhoBareCollectionConstructorsWrapped
  openCanonicalPreservesWrappedConstructorTyping :=
    rhoContextualOpenSection_preservesWrappedConstructorTyping
  equationsRetypable := rhoContinuationRetyping_equationsRetypable
  reflectivePresentationsRetypable :=
    rhoContinuationRetyping_reflectivePresentationsRetypable
  sourceEnvelopeStable := .hole "Proc"
  redexRetypable := rhoContinuationRetyping_redexRetypable
  wrappable := rhoContinuationRetyping_wrappable

/-- Forgetting the continued structure recovers the exact rho iGSLT. -/
theorem rhoCIGSLT_forget : CIGSLT.forget.obj rhoCIGSLT = rhoIGSLT :=
  rfl

/-- Positive control: the generated continuation signature assigns the
wrapped sort to rho's input continuation. -/
theorem rho_input_continuation_retyped :
    (costBaseConstructor rhoInteractionCut rhoCalc.terms[5]).params[1]? =
      some (.abstraction "p"
        (.arrow (.base (costBaseSortName "Name"))
          (.base costWrappedSortName))) := by
  simp [costBaseConstructor, costBaseParameter, isSelectedContinuation, rhoCalc,
    rhoInteractionCut_program_constructor_value,
    rhoInteractionCut_environment_constructor_value,
    rhoInteractionCut_program_continuation_index,
    rhoInteractionCut_environment_continuation_index,
    mapParameterType, costWrappedTypeExpr, costBaseTypeExpr,
    rhoIGSLT, rhoInteractivePresentation, TypeDecl.plain,
    TypeExpr.name, TypeExpr.proc, TypeExpr.funType, TypeExpr.baseType,
    costBaseSortName, costWrappedSortName]

/-- Negative control: rho's channel/subject argument remains in the base name
sort; continuation retyping does not seal or re-sort interaction subjects. -/
theorem rho_input_subject_not_retyped :
    (costBaseConstructor rhoInteractionCut rhoCalc.terms[5]).params[0]? =
      some (.simple "n" (.base (costBaseSortName "Name"))) := by
  simp [costBaseConstructor, costBaseParameter, isSelectedContinuation, rhoCalc,
    rhoInteractionCut_program_constructor_value,
    rhoInteractionCut_environment_constructor_value,
    rhoInteractionCut_program_continuation_index,
    rhoInteractionCut_environment_continuation_index,
    mapParameterType, costWrappedTypeExpr, costBaseTypeExpr,
    rhoIGSLT, rhoInteractivePresentation, TypeDecl.plain,
    TypeExpr.name, TypeExpr.proc, TypeExpr.funType, TypeExpr.baseType,
    costBaseSortName, costWrappedSortName]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
