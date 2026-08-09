import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
import Mettapedia.GSLT.LanguageDef.ReflectiveEquationOccurrence

/-!
# A cross-boundary ordering canary for compact rho Cost normalization

This module tests exact compact generator invariance on an authored first-layer
rho Cost edge.  The left endpoint contains a base-colour Quote/Drop redex below
a wrapped process frame; the right endpoint contains its direct free-name
representative.  Both endpoints inhabit one exact typed open fibre.

The definitions below are deliberately explicit.  The eventual negative
theorem must compare independently normalized proof-relevant elaborations; it
must not infer inequality from a raw or ill-typed mixed-colour term.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

/-- The exact free context of the proposed first-layer counterexample. -/
def rhoCutOrderFree : FreeTypeContext :=
  FreeTypeContext.ofList
    [("0", .base (costBaseSortName "Name")),
      ("a", .base (costBaseSortName "Name"))]

def rhoCutOrderBaseDrop (name : Pattern) : Pattern :=
  .apply (costBaseConstructorName "PDrop") [name]

def rhoCutOrderBaseQuote (process : Pattern) : Pattern :=
  .apply (costBaseConstructorName "NQuote") [process]

def rhoCutOrderWrappedDrop (name : Pattern) : Pattern :=
  .apply (costWrappedConstructorName "PDrop") [name]

def rhoCutOrderParallel (processes : List Pattern) : Pattern :=
  .collection .hashBag processes none

/-- The base-colour Quote/Drop redex that becomes a foreign boundary inside
the surrounding wrapped process region. -/
def rhoCutOrderRedex : Pattern :=
  rhoCutOrderBaseQuote (rhoCutOrderBaseDrop (.fvar "0"))

def rhoCutOrderLeftPattern : Pattern :=
  rhoCutOrderParallel
    [rhoCutOrderWrappedDrop rhoCutOrderRedex,
      rhoCutOrderWrappedDrop (.fvar "a")]

def rhoCutOrderRightPattern : Pattern :=
  rhoCutOrderParallel
    [rhoCutOrderWrappedDrop (.fvar "0"),
      rhoCutOrderWrappedDrop (.fvar "a")]

private theorem rhoRule_mem (index : Fin 4) :
    rhoCalc.terms[index] ∈ rhoCalc.terms := by
  exact List.getElem_mem (by simp [rhoCalc]; omega)

private theorem rhoCutOrderZero_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (.fvar "0") (.base (costBaseSortName "Name")) :=
  .fvar (by simp [rhoCutOrderFree, FreeTypeContext.ofList])

private theorem rhoCutOrderA_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (.fvar "a") (.base (costBaseSortName "Name")) :=
  .fvar (by simp [rhoCutOrderFree, FreeTypeContext.ofList])

private theorem rhoCutOrderBaseDropZero_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (rhoCutOrderBaseDrop (.fvar "0"))
      (.base (costBaseSortName "Proc")) := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[1])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _ (rhoRule_mem 1)
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseDropConstructor_params]
    exact .cons (by trivial) rfl rhoCutOrderZero_typed .nil

private theorem rhoCutOrderRedex_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoCutOrderRedex (.base (costBaseSortName "Name")) := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[2])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _ (rhoRule_mem 2)
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseQuoteConstructor_params]
    exact .cons (by trivial) rfl rhoCutOrderBaseDropZero_typed .nil

private def rhoCutOrderDropConstructor :
    AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[1], rhoRule_mem 1⟩

private theorem rhoCutOrderDrop_selected :
    rhoCutOrderDropConstructor ∈
      rhoContinuationRetyping.wrappedConstructors := by
  apply (rhoContinuationRetyping.mem_wrappedConstructors_iff
    rhoCutOrderDropConstructor).2
  constructor <;> decide

private theorem rhoCutOrderWrappedDrop_mem :
    costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1] ∈
      rhoCIGSLT.costWholeLanguage.terms := by
  change costWrappedConstructor (theory := rhoCIGSLT.theory)
      rhoCutOrderDropConstructor.1 ∈ rhoCIGSLT.costWholeLanguage.terms
  exact rhoCIGSLT.costWrappedConstructor_mem_costWhole
    rhoCutOrderDropConstructor rhoCutOrderDrop_selected

private theorem rhoCutOrderWrappedDrop_typed (name : Pattern)
    (typed : HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree [] name
      (.base (costBaseSortName "Name"))) :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (rhoCutOrderWrappedDrop name) (.base costWrappedSortName) := by
  apply HasType.constructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1])
  · exact rhoCutOrderWrappedDrop_mem
  · rw [usesBareCollection_costWrappedConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costWrappedDropConstructor_params]
    exact .cons (by trivial) rfl typed .nil

private def rhoCutOrderParallelConstructor :
    AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[3], rhoRule_mem 3⟩

private theorem rhoCutOrderParallel_selected :
    rhoCutOrderParallelConstructor ∈
      rhoContinuationRetyping.wrappedConstructors := by
  apply (rhoContinuationRetyping.mem_wrappedConstructors_iff
    rhoCutOrderParallelConstructor).2
  constructor <;> decide

private theorem rhoCutOrderWrappedParallel_mem :
    costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[3] ∈
      rhoCIGSLT.costWholeLanguage.terms := by
  change costWrappedConstructor (theory := rhoCIGSLT.theory)
      rhoCutOrderParallelConstructor.1 ∈ rhoCIGSLT.costWholeLanguage.terms
  exact rhoCIGSLT.costWrappedConstructor_mem_costWhole
    rhoCutOrderParallelConstructor rhoCutOrderParallel_selected

theorem rhoCutOrderLeft_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoCutOrderLeftPattern (.base costWrappedSortName) := by
  apply HasType.collectionConstructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[3])
      (parameterName := "ps") (elementType := .base costWrappedSortName)
  · exact rhoCutOrderWrappedParallel_mem
  · exact rho_costWrappedParallelConstructor_params
  · exact .cons
      (rhoCutOrderWrappedDrop_typed rhoCutOrderRedex rhoCutOrderRedex_typed)
      (.cons
        (rhoCutOrderWrappedDrop_typed (.fvar "a") rhoCutOrderA_typed)
        (.nil [] _))

theorem rhoCutOrderRight_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoCutOrderRightPattern (.base costWrappedSortName) := by
  apply HasType.collectionConstructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[3])
      (parameterName := "ps") (elementType := .base costWrappedSortName)
  · exact rhoCutOrderWrappedParallel_mem
  · exact rho_costWrappedParallelConstructor_params
  · exact .cons
      (rhoCutOrderWrappedDrop_typed (.fvar "0") rhoCutOrderZero_typed)
      (.cons
        (rhoCutOrderWrappedDrop_typed (.fvar "a") rhoCutOrderA_typed)
        (.nil [] _))

def rhoCutOrderWrappedProcSort : LangSort rhoCIGSLT.costWholeLanguage :=
  CostStaticColor.wrapped.mapLangSort rhoCIGSLT rhoProc

def rhoCutOrderLeft : ReflectiveWellSorted.OpenTerm
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    rhoCutOrderFree [] rhoCutOrderWrappedProcSort := by
  refine ⟨rhoCutOrderLeftPattern,
    ⟨rhoCutOrderLeft_typed, rfl, rfl, ?_⟩, ?_⟩
  · simp [ScopeSafeAt, rhoCutOrderLeftPattern, rhoCutOrderParallel,
      rhoCutOrderWrappedDrop, rhoCutOrderRedex, rhoCutOrderBaseQuote,
      rhoCutOrderBaseDrop, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]
  · intro declaration membership
    simp [rhoCutOrderLeftPattern, rhoCutOrderParallel,
      rhoCutOrderWrappedDrop, rhoCutOrderRedex, rhoCutOrderBaseQuote,
      rhoCutOrderBaseDrop, binderSafeAt, binderSafeListAt]

def rhoCutOrderRight : ReflectiveWellSorted.OpenTerm
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    rhoCutOrderFree [] rhoCutOrderWrappedProcSort := by
  refine ⟨rhoCutOrderRightPattern,
    ⟨rhoCutOrderRight_typed, rfl, rfl, ?_⟩, ?_⟩
  · simp [ScopeSafeAt, rhoCutOrderRightPattern, rhoCutOrderParallel,
      rhoCutOrderWrappedDrop, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]
  · intro declaration membership
    simp [rhoCutOrderRightPattern, rhoCutOrderParallel,
      rhoCutOrderWrappedDrop, binderSafeAt, binderSafeListAt]

/-- The structural context placing the base Quote/Drop edge beneath a wrapped
Drop and beside a second wrapped process. -/
def rhoCutOrderContext : OneHoleContext :=
  .collection .hashBag []
    (.apply (costWrappedConstructorName "PDrop") [] .hole [])
    [rhoCutOrderWrappedDrop (.fvar "a")] none

/-- Proof-relevant occurrence underlying the mixed-colour Quote/Drop edge.
The generated declaration, redex context, and representative equality remain
available as data before support erasure. -/
def rhoCutOrderGeneratorWitness :
    ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage rhoCutOrderLeft.1 rhoCutOrderRight.1 := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl
  have membership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            rhoReflectionProfile.presentations
          simp [rhoReflectionProfile])
  have representatives :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          rhoCutOrderRedex =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (.fvar "0") := by
    simp [declaration, rhoCutOrderRedex, rhoCutOrderBaseQuote,
      rhoCutOrderBaseDrop,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
      mapReflectivePresentation,
      rhoReflectivePresentation,
      CostStaticColor.constructorTag,
      costBaseConstructorName, costBaseConstructorTag]
  simpa [rhoCutOrderContext, rhoCutOrderLeft, rhoCutOrderRight,
    rhoCutOrderLeftPattern, rhoCutOrderRightPattern,
    rhoCutOrderParallel, rhoCutOrderWrappedDrop,
    OneHoleContext.fill] using
      (ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness.reflective
        rhoCutOrderContext ⟨declaration, membership⟩ representatives)

/-- The two checked endpoints are joined by one generated reflective edge in
their exact open typing fibre. -/
theorem rhoCutOrder_generator :
    ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (.base rhoCutOrderWrappedProcSort.1) rhoCutOrderLeft
      rhoCutOrderRight := by
  exact rhoCutOrderGeneratorWitness.erase

/-! ## Explicit outer wrapped-region plan -/

private def rhoCutOrderWrappedDropDeclared :
    rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.wrapped rhoCutOrderDropConstructor, rhoCutOrderDrop_selected⟩

private theorem rhoCutOrderWrappedDropRole :
    rhoCIGSLT.declaredCostConstructorRole rhoCutOrderWrappedDropDeclared =
      .static .wrapped := by
  rfl

private def rhoCutOrderWrappedDropPreimage :
    CostStaticConstructorPreimage rhoCIGSLT .wrapped
      rhoCutOrderWrappedDropDeclared :=
  costStaticConstructorPreimage rhoCIGSLT .wrapped
    rhoCutOrderWrappedDropDeclared rhoCutOrderWrappedDropRole

private theorem rhoCutOrderWrappedDrop_notBare :
    ¬ UsesBareCollection
      rhoCutOrderWrappedDropPreimage.sourceConstructor.1 := by
  simp [rhoCutOrderWrappedDropPreimage, costStaticConstructorPreimage,
    rhoCutOrderWrappedDropDeclared, rhoCutOrderDropConstructor,
    UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
    TypeExpr.baseType]

private def rhoCutOrderWrappedFvarPlan (outer : OneHoleContext)
    (name : String)
    (lookup : rhoCutOrderFree name =
      some (.base (costBaseSortName "Name"))) :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] outer (.fvar name) (.base "Name") :=
  .fvar (by
    simpa [mapTypeExpr, CostStaticColor.symbols,
      costWrappedStaticSymbols, rhoCIGSLT, rhoIGSLT,
      rhoInteractivePresentation, rhoCalc, TypeDecl.plain,
      show "Name" ≠ "Proc" by decide] using lookup)

private def rhoCutOrderWrappedDropFvarPlan (outer : OneHoleContext)
    (name : String)
    (lookup : rhoCutOrderFree name =
      some (.base (costBaseSortName "Name"))) :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] outer (rhoCutOrderWrappedDrop (.fvar name)) (.base "Proc") := by
  apply CostStaticRegionPlan.application rhoCutOrderWrappedDropDeclared rfl
    rhoCutOrderWrappedDropRole rhoCutOrderWrappedDropPreimage
  · exact rhoCutOrderWrappedDrop_notBare
  · exact .cons (by trivial) rfl
      (rhoCutOrderWrappedFvarPlan
        (outer.comp
          (.apply (costWrappedConstructorName "PDrop") [] .hole []))
        name lookup)
      .nil

private def rhoCutOrderParallelChoice : CostCollectionTypingChoice :=
  .bare rhoCalc.terms[3] (.base "Proc")

private theorem rhoCutOrderParallelChoice_mem :
    rhoCutOrderParallelChoice ∈
      costStaticCollectionTypingChoices rhoCIGSLT .wrapped rhoCutOrderFree []
        .hashBag
        [rhoCutOrderWrappedDrop rhoCutOrderRedex,
          rhoCutOrderWrappedDrop (.fvar "a")]
        (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (.base "Proc")) := by
  have membership : rhoCalc.terms[3] ∈
      rhoCIGSLT.theory.presentation.presentation.language.terms := by
    change rhoCalc.terms[3] ∈ rhoCalc.terms
    exact rhoRule_mem 3
  apply mem_costStaticCollectionTypingChoices_complete
  right
  refine ⟨rhoCalc.terms[3], .base "Proc", rfl, membership, ?_,
    rfl, "ps", rfl, rfl⟩
  apply rhoCIGSLT.bareCollectionConstructorsWrapped _ membership
  exact ⟨"ps", .hashBag, .base "Proc", rfl⟩

private theorem rhoCutOrderRedex_wellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      rhoCutOrderFree []
      (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
        (.base "Name"))
      rhoCutOrderRedex := by
  refine ⟨⟨?_, rfl, rfl, ?_⟩, ?_⟩
  · simpa [mapTypeExpr, CostStaticColor.symbols,
      costWrappedStaticSymbols, rhoCIGSLT, rhoIGSLT,
      rhoInteractivePresentation, rhoCalc, TypeDecl.plain,
      show "Name" ≠ "Proc" by decide] using rhoCutOrderRedex_typed
  · simp [ScopeSafeAt, rhoCutOrderRedex, rhoCutOrderBaseQuote,
      rhoCutOrderBaseDrop, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]
  · intro declaration membership
    simp [rhoCutOrderRedex, rhoCutOrderBaseQuote, rhoCutOrderBaseDrop,
      binderSafeAt, binderSafeListAt]

private theorem rhoCutOrderBoundaryCertificate_exists :
    ∃ certificate,
      certifyCostRegionBoundary? rhoCIGSLT .wrapped rhoCutOrderFree []
          (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
            (.base "Name"))
          rhoCutOrderRedex =
        some certificate := by
  apply exists_certifyCostRegionBoundary?_eq_some
  · exact ⟨.base "Name", decodeCostStaticTypeExpr_mapTypeExpr _ _ _⟩
  · exact rhoCutOrderRedex_wellSorted

private noncomputable def rhoCutOrderBoundaryCertificate :=
  Classical.choose rhoCutOrderBoundaryCertificate_exists

private theorem rhoCutOrderBoundaryCertificate_spec :
    certifyCostRegionBoundary? rhoCIGSLT .wrapped rhoCutOrderFree []
        (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (.base "Name"))
        rhoCutOrderRedex =
      some rhoCutOrderBoundaryCertificate :=
  Classical.choose_spec rhoCutOrderBoundaryCertificate_exists

/-- Public proof-relevant boundary witness used by exactness regressions.
The executable certifier remains the sole source of the witness. -/
noncomputable def rhoCutOrderBoundaryWitness :
    CertifiedCostRegionBoundary rhoCIGSLT .wrapped rhoCutOrderFree []
      (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
        (.base "Name")) rhoCutOrderRedex :=
  rhoCutOrderBoundaryCertificate

theorem rhoCutOrderBoundaryWitness_spec :
    certifyCostRegionBoundary? rhoCIGSLT .wrapped rhoCutOrderFree []
        (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (.base "Name")) rhoCutOrderRedex =
      some rhoCutOrderBoundaryWitness :=
  rhoCutOrderBoundaryCertificate_spec

private def rhoCutOrderBaseQuoteConstructor :
    AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[2], rhoRule_mem 2⟩

private def rhoCutOrderBaseQuoteDeclared :
    rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.base rhoCutOrderBaseQuoteConstructor, True.intro⟩

private theorem rhoCutOrderBaseQuoteRole :
    rhoCIGSLT.declaredCostConstructorRole rhoCutOrderBaseQuoteDeclared =
      .static .base := by
  rfl

private theorem rhoCutOrderBaseQuoteOutsideWrapped :
    rhoCIGSLT.declaredCostConstructorRole rhoCutOrderBaseQuoteDeclared ≠
      .static .wrapped := by
  rw [rhoCutOrderBaseQuoteRole]
  decide

private noncomputable def rhoCutOrderWrappedBoundaryPlan
    (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] outer rhoCutOrderRedex (.base "Name") :=
  .boundaryApplication rhoCutOrderBaseQuoteDeclared rfl
    rhoCutOrderBaseQuoteOutsideWrapped rhoCutOrderBoundaryWitness
    rhoCutOrderBoundaryWitness_spec

private noncomputable def rhoCutOrderWrappedDropBoundaryPlan
    (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] outer (rhoCutOrderWrappedDrop rhoCutOrderRedex) (.base "Proc") := by
  apply CostStaticRegionPlan.application rhoCutOrderWrappedDropDeclared rfl
    rhoCutOrderWrappedDropRole rhoCutOrderWrappedDropPreimage
  · exact rhoCutOrderWrappedDrop_notBare
  · exact .cons (by trivial) rfl
      (rhoCutOrderWrappedBoundaryPlan
        (outer.comp
          (.apply (costWrappedConstructorName "PDrop") [] .hole [])))
      .nil

private theorem rhoCutOrderRightParallelChoice_mem :
    rhoCutOrderParallelChoice ∈
      costStaticCollectionTypingChoices rhoCIGSLT .wrapped rhoCutOrderFree []
        .hashBag
        [rhoCutOrderWrappedDrop (.fvar "0"),
          rhoCutOrderWrappedDrop (.fvar "a")]
        (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (.base "Proc")) := by
  have membership : rhoCalc.terms[3] ∈
      rhoCIGSLT.theory.presentation.presentation.language.terms := by
    change rhoCalc.terms[3] ∈ rhoCalc.terms
    exact rhoRule_mem 3
  apply mem_costStaticCollectionTypingChoices_complete
  right
  refine ⟨rhoCalc.terms[3], .base "Proc", rfl, membership, ?_,
    rfl, "ps", rfl, rfl⟩
  apply rhoCIGSLT.bareCollectionConstructorsWrapped _ membership
  exact ⟨"ps", .hashBag, .base "Proc", rfl⟩

private noncomputable def rhoCutOrderLeftPlan :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] .hole rhoCutOrderLeftPattern (.base "Proc") := by
  apply CostStaticRegionPlan.collection rhoCutOrderParallelChoice
    rhoCutOrderParallelChoice_mem
  exact .cons
    (rhoCutOrderWrappedDropBoundaryPlan
      (OneHoleContext.hole.comp (.collection .hashBag [] .hole
        [rhoCutOrderWrappedDrop (.fvar "a")] none)))
    (.cons
      (rhoCutOrderWrappedDropFvarPlan
        (OneHoleContext.hole.comp (.collection .hashBag
          [rhoCutOrderWrappedDrop rhoCutOrderRedex] .hole [] none))
        "a" (by simp [rhoCutOrderFree, FreeTypeContext.ofList]))
      .nil)

private def rhoCutOrderRightPlan :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] .hole rhoCutOrderRightPattern (.base "Proc") := by
  apply CostStaticRegionPlan.collection rhoCutOrderParallelChoice
    rhoCutOrderRightParallelChoice_mem
  exact .cons
    (rhoCutOrderWrappedDropFvarPlan
      (OneHoleContext.hole.comp (.collection .hashBag [] .hole
        [rhoCutOrderWrappedDrop (.fvar "a")] none))
      "0" (by simp [rhoCutOrderFree, FreeTypeContext.ofList]))
    (.cons
      (rhoCutOrderWrappedDropFvarPlan
        (OneHoleContext.hole.comp (.collection .hashBag
          [rhoCutOrderWrappedDrop (.fvar "0")] .hole [] none))
        "a" (by simp [rhoCutOrderFree, FreeTypeContext.ofList]))
      .nil)

/-! ## Explicit base boundary tree -/

private def rhoCutOrderBaseDropDeclared :
    rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.base rhoCutOrderDropConstructor, True.intro⟩

private theorem rhoCutOrderBaseDropRole :
    rhoCIGSLT.declaredCostConstructorRole rhoCutOrderBaseDropDeclared =
      .static .base := by
  rfl

private def rhoCutOrderBaseDropPreimage :
    CostStaticConstructorPreimage rhoCIGSLT .base
      rhoCutOrderBaseDropDeclared :=
  costStaticConstructorPreimage rhoCIGSLT .base rhoCutOrderBaseDropDeclared
    rhoCutOrderBaseDropRole

private theorem rhoCutOrderBaseDrop_notBare :
    ¬ UsesBareCollection rhoCutOrderBaseDropPreimage.sourceConstructor.1 := by
  simp [rhoCutOrderBaseDropPreimage, costStaticConstructorPreimage,
    rhoCutOrderBaseDropDeclared, rhoCutOrderDropConstructor,
    UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
    TypeExpr.baseType]

private def rhoCutOrderBaseQuotePreimage :
    CostStaticConstructorPreimage rhoCIGSLT .base
      rhoCutOrderBaseQuoteDeclared :=
  costStaticConstructorPreimage rhoCIGSLT .base rhoCutOrderBaseQuoteDeclared
    rhoCutOrderBaseQuoteRole

private theorem rhoCutOrderBaseQuote_notBare :
    ¬ UsesBareCollection rhoCutOrderBaseQuotePreimage.sourceConstructor.1 := by
  simp [rhoCutOrderBaseQuotePreimage, costStaticConstructorPreimage,
    rhoCutOrderBaseQuoteDeclared, rhoCutOrderBaseQuoteConstructor,
    UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
    TypeExpr.baseType]

private def rhoCutOrderBaseFvarPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer (.fvar "0") (.base "Name") :=
  .fvar (by
    simp [rhoCutOrderFree, FreeTypeContext.ofList, mapTypeExpr,
      CostStaticColor.symbols, costBaseStaticSymbols,
      costBasePresentationSymbols])

private def rhoCutOrderBaseDropPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer (rhoCutOrderBaseDrop (.fvar "0")) (.base "Proc") := by
  apply CostStaticRegionPlan.application rhoCutOrderBaseDropDeclared rfl
    rhoCutOrderBaseDropRole rhoCutOrderBaseDropPreimage
  · exact rhoCutOrderBaseDrop_notBare
  · exact .cons (by trivial) rfl
      (rhoCutOrderBaseFvarPlan
        (outer.comp
          (.apply (costBaseConstructorName "PDrop") [] .hole [])))
      .nil

private def rhoCutOrderBaseRedexPlan :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] .hole rhoCutOrderRedex (.base "Name") := by
  apply CostStaticRegionPlan.application rhoCutOrderBaseQuoteDeclared rfl
    rhoCutOrderBaseQuoteRole rhoCutOrderBaseQuotePreimage
  · exact rhoCutOrderBaseQuote_notBare
  · exact .cons (by trivial) rfl
      (rhoCutOrderBaseDropPlan
        (OneHoleContext.hole.comp
          (.apply (costBaseConstructorName "NQuote") [] .hole [])))
      .nil

private def rhoCutOrderBaseNameSort : LangSort rhoCIGSLT.costWholeLanguage :=
  CostStaticColor.base.mapLangSort rhoCIGSLT rhoName

private def rhoCutOrderRedexTerm :
    OpenTerm rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoCutOrderBaseNameSort :=
  ⟨rhoCutOrderRedex, rhoCutOrderRedex_wellSorted.1⟩

def rhoCutOrderBaseRedexNode :
    CostStaticRegionNode rhoCIGSLT .base rhoCutOrderFree :=
  CostStaticRegionNode.ofPlan rhoCutOrderRedexTerm rhoCutOrderBaseRedexPlan rfl

/-- The base Quote/Drop witness has no opposite-colour boundary children. -/
def rhoCutOrderBaseRedexChildren :
    CostRegionBoundaryTrees rhoCIGSLT rhoCutOrderFree .base
      rhoCutOrderBaseRedexNode.finiteBoundaryTable := by
  apply CostRegionBoundaryTrees.ofEntriesEqNil
  rfl

/-- The raw constructor form is kept at its intrinsic dependent indices;
the compact witness below transports those indices explicitly. -/
def rhoCutOrderBaseRedexStaticTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree
      rhoCutOrderBaseRedexNode.targetBound []
      rhoCutOrderBaseRedexNode.term.1
      (.base (CostStaticColor.base.mapLangSort rhoCIGSLT
        rhoCutOrderBaseRedexNode.sourceSort).1) :=
  .static rhoCutOrderBaseRedexNode rhoCutOrderBaseRedexChildren

theorem rhoCutOrderBaseRedexNode_targetBound :
    rhoCutOrderBaseRedexNode.targetBound = [] := by
  rfl

theorem rhoCutOrderBaseRedexNode_term_pattern :
    rhoCutOrderBaseRedexNode.term.1 = rhoCutOrderRedex := by
  rfl

theorem rhoCutOrderBaseRedexNode_resultType :
    (.base (CostStaticColor.base.mapLangSort rhoCIGSLT
      rhoCutOrderBaseRedexNode.sourceSort).1 : TypeExpr) =
        .base (costBaseSortName "Name") := by
  rfl

def rhoCutOrderBaseRedexTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] rhoCutOrderRedex
      (.base (costBaseSortName "Name")) :=
  CostRegionTree.reindexType rhoCutOrderBaseRedexNode_resultType
    (CostRegionTree.reindexPattern rhoCutOrderBaseRedexNode_term_pattern
      (CostRegionTree.reindexAvailable rhoCutOrderBaseRedexNode_targetBound
        rhoCutOrderBaseRedexStaticTree))

theorem rhoCutOrderBaseRedexNode_skeleton_pattern :
    rhoCutOrderBaseRedexNode.skeleton.1 =
      .apply "NQuote"
        [.apply "PDrop"
          [.fvar (costRegionSourceVariableName "0")]] := by
  rfl

private theorem rhoCutOrderBaseRedexNode_sourceCanonical :
    (rhoCIGSLT.openCanonical.normalize
      rhoCutOrderBaseRedexNode.skeleton).1 =
        .fvar (costRegionSourceVariableName "0") := by
  change Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
      rhoCutOrderBaseRedexNode.skeleton.1 = _
  rw [rhoCutOrderBaseRedexNode_skeleton_pattern]
  exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize_quote_drop_example _

private theorem rhoCutOrderBaseRedexNode_normalizedThickenedSkeletonRaw :
    rhoCutOrderBaseRedexNode.normalizedThickenedSkeletonRaw =
      .fvar (costRegionSourceVariableName "0") := by
  unfold CostStaticRegionNode.normalizedThickenedSkeletonRaw
  rw [
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      rhoCutOrderBaseRedexNode.thinning (by rfl)]
  unfold normalizeCostStaticStratum
  rw [rhoCutOrderBaseRedexNode_sourceCanonical]
  rfl

private theorem rhoCutOrderBaseRedexTree_normalize :
    rhoCutOrderBaseRedexTree.normalize.pattern = .fvar "0" := by
  unfold rhoCutOrderBaseRedexTree
  rw [CostRegionTree.reindexType_normalize,
    CostRegionTree.reindexPattern_normalize,
    CostRegionTree.reindexAvailable_normalize]
  apply Eq.trans
    (CostRegionTree.normalize_static_eq_normalizeRaw_of_entries_eq_nil
      rhoCutOrderBaseRedexNode rhoCutOrderBaseRedexChildren (by rfl))
  unfold CostStaticRegionNode.normalizeRaw
    CostStaticRegionNode.normalizeRawWith
  rw [CostStaticRegionNode.normalizedThickenedSkeleton_pattern,
    rhoCutOrderBaseRedexNode_normalizedThickenedSkeletonRaw]
  rw [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton_original]
  simp [TypedCostRegionBoundaryTable.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute,
    ReflectiveContextSupport.substituteAt]
  rw [show rhoCutOrderBaseRedexNode.targetBound.length = 0 by rfl]
  exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero _ _

/-! ## The two explicit full elaborations -/

private theorem natPair_mono {first second third fourth : Nat}
    (firstLe : first ≤ third) (secondLe : second ≤ fourth) :
    Nat.pair first second ≤ Nat.pair third fourth := by
  have leftStep : Nat.pair first second ≤ Nat.pair third second := by
    rcases firstLe.lt_or_eq with strict | equality
    · exact (Nat.pair_lt_pair_left second strict).le
    · subst third
      exact Nat.le_refl _
  have rightStep : Nat.pair third second ≤ Nat.pair third fourth := by
    rcases secondLe.lt_or_eq with strict | equality
    · exact (Nat.pair_lt_pair_right third strict).le
    · subst fourth
      exact Nat.le_refl _
  exact leftStep.trans rightStep

private theorem charListCode_append_le_append_of_le (stem : List Char)
    {left right : List Char}
    (strict : charListCode left ≤ charListCode right) :
    charListCode (stem ++ left) ≤ charListCode (stem ++ right) := by
  induction stem with
  | nil => simpa
  | cons character remainder inductionHypothesis =>
      simp only [List.cons_append, charListCode]
      exact Nat.succ_le_succ
        (natPair_mono (Nat.le_refl _) inductionHypothesis)

private theorem charListCode_append_lt_append_of_lt (stem : List Char)
    {left right : List Char}
    (strict : charListCode left < charListCode right) :
    charListCode (stem ++ left) < charListCode (stem ++ right) := by
  induction stem with
  | nil => simpa
  | cons character remainder inductionHypothesis =>
      simp only [List.cons_append, charListCode]
      exact Nat.succ_lt_succ
        (Nat.pair_lt_pair_right character.toNat inductionHypothesis)

private theorem charListCode_zero_le_repr (number : Nat) :
    charListCode ['0'] ≤ charListCode number.repr.toList := by
  rw [Nat.toList_repr]
  cases digits : Nat.toDigits 10 number with
  | nil => exact (Nat.toDigits_ne_nil digits).elim
  | cons character remainder =>
      have digit : character.isDigit :=
        Nat.isDigit_of_mem_toDigits (b := 10) (n := number)
          (by omega) (by omega) (by rw [digits]; simp)
      have lower : '0'.toNat ≤ character.toNat :=
        (Char.isDigit_iff_toNat.mp digit).1
      simp only [charListCode]
      exact Nat.succ_le_succ
        (natPair_mono lower (Nat.zero_le _))

private theorem rhoCutOrderSourceZero_lt_sourceA :
    stringCode (costRegionSourceVariableName "0") <
      stringCode (costRegionSourceVariableName "a") := by
  have suffix : charListCode ['0'] < charListCode ['a'] := by decide
  have full := charListCode_append_lt_append_of_lt
    costRegionSourceVariableTag.toList suffix
  simpa [stringCode, costRegionSourceVariableName,
    String.toList_append] using full

private theorem rhoCutOrderSourceA_lt_boundary
    (boundary : CostRegionBoundary) :
    stringCode (costRegionSourceVariableName "a") <
      stringCode (costRegionBoundaryVariableName boundary) := by
  have suffixFixed : charListCode "source:a".toList <
      charListCode ("boundary:".toList ++ ['0']) := by decide
  have suffixLower : charListCode ("boundary:".toList ++ ['0']) ≤
      charListCode ("boundary:".toList ++ boundary.code.repr.toList) :=
    charListCode_append_le_append_of_le "boundary:".toList
      (charListCode_zero_le_repr boundary.code)
  have suffix := suffixFixed.trans_le suffixLower
  have full := charListCode_append_lt_append_of_lt
    "$cost:region-".toList suffix
  simpa [stringCode, costRegionSourceVariableName,
    costRegionSourceVariableTag, costRegionBoundaryVariableName,
    costRegionBoundaryVariableTag, String.toList_append] using full

private theorem rhoPDrop_patternCode_lt_of_stringCode_lt
    {left right : String} (strict : stringCode left < stringCode right) :
    patternCode (.apply "PDrop" [.fvar left]) <
      patternCode (.apply "PDrop" [.fvar right]) := by
  have freeVariableStep : patternCode (.fvar left) <
      patternCode (.fvar right) := by
    simpa [patternCode] using Nat.pair_lt_pair_right 1 strict
  have argumentStep : patternListCode [.fvar left] <
      patternListCode [.fvar right] := by
    simpa [patternListCode] using
      Nat.succ_lt_succ (Nat.pair_lt_pair_left 0 freeVariableStep)
  simpa [patternCode] using Nat.pair_lt_pair_right 2
    (Nat.pair_lt_pair_right (stringCode "PDrop") argumentStep)

private theorem sortPatterns_pair_eq_of_le (left right : Pattern)
    (ordered : patternCode left ≤ patternCode right) :
    sortPatterns [left, right] = [left, right] := by
  let relation : Pattern → Pattern → Prop :=
    fun first second => patternCode first ≤ patternCode second
  letI : Std.Total relation :=
    ⟨fun first second => Nat.le_total (patternCode first) (patternCode second)⟩
  letI : IsTrans Pattern relation :=
    ⟨fun _ _ _ firstLe secondLe => Nat.le_trans firstLe secondLe⟩
  letI : Std.Antisymm relation :=
    ⟨fun first second firstLe secondLe =>
      patternCode_injective (Nat.le_antisymm firstLe secondLe)⟩
  apply List.mergeSort_eq_self
  simp [ordered]

private theorem sortPatterns_pair_eq_swap_of_le (left right : Pattern)
    (ordered : patternCode right ≤ patternCode left) :
    sortPatterns [left, right] = [right, left] := by
  calc
    sortPatterns [left, right] = sortPatterns [right, left] :=
      sortPatterns_eq_of_perm (List.Perm.swap left right []).symm
    _ = [right, left] := sortPatterns_pair_eq_of_le right left ordered

private theorem canonicalize_parallel_two_drops_eq_of_le
    (left right : String)
    (ordered : patternCode (.apply "PDrop" [.fvar left]) ≤
      patternCode (.apply "PDrop" [.fvar right])) :
    canonicalize
        (.collection .hashBag
          [.apply "PDrop" [.fvar left],
            .apply "PDrop" [.fvar right]] none) =
      .collection .hashBag
        [.apply "PDrop" [.fvar left],
          .apply "PDrop" [.fvar right]] none := by
  simp [canonicalize, canonicalizeList, normalizeBagElements,
    bagSplice, collapseBag, sortPatterns_pair_eq_of_le _ _ ordered]

private theorem canonicalize_parallel_two_drops_eq_swap_of_le
    (left right : String)
    (ordered : patternCode (.apply "PDrop" [.fvar right]) ≤
      patternCode (.apply "PDrop" [.fvar left])) :
    canonicalize
        (.collection .hashBag
          [.apply "PDrop" [.fvar left],
            .apply "PDrop" [.fvar right]] none) =
      .collection .hashBag
        [.apply "PDrop" [.fvar right],
          .apply "PDrop" [.fvar left]] none := by
  simp [canonicalize, canonicalizeList, normalizeBagElements,
    bagSplice, collapseBag, sortPatterns_pair_eq_swap_of_le _ _ ordered]

private theorem rhoCutOrderLeftPlan_rootStatic :
    rhoCutOrderLeftPlan.isStaticRoot = true := by
  unfold rhoCutOrderLeftPlan
  rfl

private theorem rhoCutOrderRightPlan_rootStatic :
    rhoCutOrderRightPlan.isStaticRoot = true := by
  unfold rhoCutOrderRightPlan
  rfl

noncomputable def rhoCutOrderLeftNode :
    CostStaticRegionNode rhoCIGSLT .wrapped rhoCutOrderFree :=
  CostStaticRegionNode.ofPlan (sourceSort := rhoProc)
    rhoCutOrderLeft.toCore rhoCutOrderLeftPlan rhoCutOrderLeftPlan_rootStatic

def rhoCutOrderRightNode :
    CostStaticRegionNode rhoCIGSLT .wrapped rhoCutOrderFree :=
  CostStaticRegionNode.ofPlan (sourceSort := rhoProc)
    rhoCutOrderRight.toCore rhoCutOrderRightPlan rhoCutOrderRightPlan_rootStatic

theorem rhoCutOrderLeftNode_skeleton_pattern :
    rhoCutOrderLeftNode.skeleton.1 =
      .collection .hashBag
        [.apply "PDrop"
            [.fvar (costRegionBoundaryVariableName
              rhoCutOrderBoundaryWitness.typed.boundary)],
          .apply "PDrop"
            [.fvar (costRegionSourceVariableName "a")]] none := by
  rfl

theorem rhoCutOrderRightNode_skeleton_pattern :
    rhoCutOrderRightNode.skeleton.1 =
      .collection .hashBag
        [.apply "PDrop" [.fvar (costRegionSourceVariableName "0")],
          .apply "PDrop" [.fvar (costRegionSourceVariableName "a")]] none := by
  rfl

private theorem rhoCutOrderLeftNode_sourceCanonical :
    (rhoCIGSLT.openCanonical.normalize rhoCutOrderLeftNode.skeleton).1 =
      .collection .hashBag
        [.apply "PDrop" [.fvar (costRegionSourceVariableName "a")],
          .apply "PDrop"
            [.fvar (costRegionBoundaryVariableName
              rhoCutOrderBoundaryWitness.typed.boundary)]] none := by
  change canonicalize rhoCutOrderLeftNode.skeleton.1 = _
  rw [rhoCutOrderLeftNode_skeleton_pattern]
  exact canonicalize_parallel_two_drops_eq_swap_of_le _ _
    (rhoPDrop_patternCode_lt_of_stringCode_lt
      (rhoCutOrderSourceA_lt_boundary
        rhoCutOrderBoundaryWitness.typed.boundary)).le

private theorem rhoCutOrderRightNode_sourceCanonical :
    (rhoCIGSLT.openCanonical.normalize rhoCutOrderRightNode.skeleton).1 =
      .collection .hashBag
        [.apply "PDrop" [.fvar (costRegionSourceVariableName "0")],
          .apply "PDrop" [.fvar (costRegionSourceVariableName "a")]] none := by
  change canonicalize rhoCutOrderRightNode.skeleton.1 = _
  rw [rhoCutOrderRightNode_skeleton_pattern]
  exact canonicalize_parallel_two_drops_eq_of_le _ _
    (rhoPDrop_patternCode_lt_of_stringCode_lt
      rhoCutOrderSourceZero_lt_sourceA).le

private theorem rhoCutOrderLeftNode_normalizedThickenedSkeletonRaw :
    rhoCutOrderLeftNode.normalizedThickenedSkeletonRaw =
      .collection .hashBag
        [rhoCutOrderWrappedDrop (.fvar (costRegionSourceVariableName "a")),
          rhoCutOrderWrappedDrop
            (.fvar (costRegionBoundaryVariableName
              rhoCutOrderBoundaryWitness.typed.boundary))] none := by
  unfold CostStaticRegionNode.normalizedThickenedSkeletonRaw
  rw [
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      rhoCutOrderLeftNode.thinning (by rfl)]
  unfold normalizeCostStaticStratum
  rw [rhoCutOrderLeftNode_sourceCanonical]
  rfl

private theorem rhoCutOrderRightNode_normalizedThickenedSkeletonRaw :
    rhoCutOrderRightNode.normalizedThickenedSkeletonRaw =
      .collection .hashBag
        [rhoCutOrderWrappedDrop (.fvar (costRegionSourceVariableName "0")),
          rhoCutOrderWrappedDrop
            (.fvar (costRegionSourceVariableName "a"))] none := by
  unfold CostStaticRegionNode.normalizedThickenedSkeletonRaw
  rw [
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      rhoCutOrderRightNode.thinning (by rfl)]
  unfold normalizeCostStaticStratum
  rw [rhoCutOrderRightNode_sourceCanonical]
  rfl

private theorem rhoCutOrderWrappedNameType :
    (.base (costBaseSortName "Name") : TypeExpr) =
      mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
        (.base "Name") := by
  simp [mapTypeExpr, CostStaticColor.symbols,
    costWrappedStaticSymbols, rhoCIGSLT, rhoIGSLT,
    rhoInteractivePresentation, rhoCalc, TypeDecl.plain,
    show "Name" ≠ "Proc" by decide]

noncomputable def rhoCutOrderBoundaryChild :
    CostRegionTree rhoCIGSLT rhoCutOrderFree
      rhoCutOrderBoundaryWitness.typed.boundary.targetSupport []
      rhoCutOrderBoundaryWitness.typed.boundary.content
      rhoCutOrderBoundaryWitness.typed.boundary.targetType :=
  CostRegionTree.reindexType
    (rhoCutOrderWrappedNameType.trans
      rhoCutOrderBoundaryWitness.targetType_eq.symm)
    (CostRegionTree.reindexPattern
      rhoCutOrderBoundaryWitness.content_eq.symm
      (CostRegionTree.reindexAvailable
        rhoCutOrderBoundaryWitness.targetSupport_eq.symm
        rhoCutOrderBaseRedexTree))

private theorem rhoCutOrderBoundaryChild_normalize :
    rhoCutOrderBoundaryChild.normalize.pattern = .fvar "0" := by
  unfold rhoCutOrderBoundaryChild
  rw [CostRegionTree.reindexType_normalize,
    CostRegionTree.reindexPattern_normalize,
    CostRegionTree.reindexAvailable_normalize,
    rhoCutOrderBaseRedexTree_normalize]

noncomputable def rhoCutOrderLeftChildren :
    CostRegionBoundaryTrees rhoCIGSLT rhoCutOrderFree .wrapped
      rhoCutOrderLeftNode.finiteBoundaryTable :=
  .cons rhoCutOrderBoundaryChild .nil

def rhoCutOrderRightChildren :
    CostRegionBoundaryTrees rhoCIGSLT rhoCutOrderFree .wrapped
      rhoCutOrderRightNode.finiteBoundaryTable := by
  apply CostRegionBoundaryTrees.ofEntriesEqNil
  rfl

noncomputable def rhoCutOrderLeftTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] rhoCutOrderLeft.1
      (.base rhoCutOrderWrappedProcSort.1) :=
  .static rhoCutOrderLeftNode rhoCutOrderLeftChildren

def rhoCutOrderRightTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] rhoCutOrderRight.1
      (.base rhoCutOrderWrappedProcSort.1) :=
  .static rhoCutOrderRightNode rhoCutOrderRightChildren

private theorem rhoCutOrderWrappedDrop_notQuote :
    ReflectiveContextSupport.isQuoteConstructor
      rhoCIGSLT.costWholeReflectionProfile
      (costWrappedConstructorName "PDrop") = false := by
  decide

private theorem rhoCutOrderLeftValues_boundaryAssignment :
    rhoCutOrderLeftChildren.normalizeValues.assignment
        rhoCutOrderLeftNode.boundaryTable
        (costRegionBoundaryVariableName
          rhoCutOrderBoundaryWitness.typed.boundary) =
      .fvar "0" := by
  change
    (CostRegionBoundaryTrees.cons rhoCutOrderBoundaryChild
      CostRegionBoundaryTrees.nil).normalizeValues.assignment
        (.cons rhoCutOrderBoundaryWitness.typed
          rhoCutOrderBoundaryWitness.content_eq .nil)
        (costRegionBoundaryVariableName
          rhoCutOrderBoundaryWitness.typed.boundary) =
      .fvar "0"
  simp only [CostRegionBoundaryTrees.normalizeValues]
  unfold TypedCostRegionBoundaryTable.Values.assignment
  rw [decodeCostRegionSourceVariableName_boundary]
  unfold TypedCostRegionBoundaryTable.Values.resolve
  simp only [if_pos]
  exact rhoCutOrderBoundaryChild_normalize

private theorem values_assignment_sourceVariable
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (name : String) :
    values.assignment table (costRegionSourceVariableName name) =
      .fvar name := by
  simp [TypedCostRegionBoundaryTable.Values.assignment]

private theorem rhoCutOrderRightTree_normalize :
    rhoCutOrderRightTree.normalize.pattern = rhoCutOrderRightPattern := by
  unfold rhoCutOrderRightTree
  apply Eq.trans
    (CostRegionTree.normalize_static_eq_normalizeRaw_of_entries_eq_nil
      rhoCutOrderRightNode rhoCutOrderRightChildren (by rfl))
  unfold CostStaticRegionNode.normalizeRaw
    CostStaticRegionNode.normalizeRawWith
  rw [CostStaticRegionNode.normalizedThickenedSkeleton_pattern,
    rhoCutOrderRightNode_normalizedThickenedSkeletonRaw]
  rw [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton_original]
  simp [TypedCostRegionBoundaryTable.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute,
    ReflectiveContextSupport.substituteAt,
    rhoCutOrderWrappedDrop_notQuote,
    rhoCutOrderRightPattern, rhoCutOrderParallel,
    rhoCutOrderWrappedDrop,
    show rhoCutOrderRightNode.targetBound.length = 0 by rfl,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

private theorem rhoCutOrderLeftTree_normalize :
    rhoCutOrderLeftTree.normalize.pattern =
      rhoCutOrderParallel
        [rhoCutOrderWrappedDrop (.fvar "a"),
          rhoCutOrderWrappedDrop (.fvar "0")] := by
  unfold rhoCutOrderLeftTree CostRegionTree.normalize
  change rhoCutOrderLeftNode.normalizeRawWith
      rhoCutOrderLeftChildren.normalizeValues = _
  unfold CostStaticRegionNode.normalizeRawWith
  rw [CostStaticRegionNode.normalizedThickenedSkeleton_pattern,
    rhoCutOrderLeftNode_normalizedThickenedSkeletonRaw]
  simp [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
    rhoCutOrderLeftValues_boundaryAssignment,
    values_assignment_sourceVariable,
    ReflectiveContextSupport.substitute,
    ReflectiveContextSupport.substituteAt,
    rhoCutOrderWrappedDrop_notQuote,
    show rhoCutOrderLeftNode.targetBound.length = 0 by rfl,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero,
    rhoCutOrderParallel, rhoCutOrderWrappedDrop]

private noncomputable def rhoCutOrderLeftElaboration :
    CostOpenElaboration rhoCIGSLT rhoCutOrderLeft :=
  ⟨rhoCutOrderLeftTree⟩

private def rhoCutOrderRightElaboration :
    CostOpenElaboration rhoCIGSLT rhoCutOrderRight :=
  ⟨rhoCutOrderRightTree⟩

private theorem rhoCutOrderLeft_costNormalizeOpen_pattern :
    (rhoCIGSLT.costNormalizeOpen rhoCutOrderLeft).1 =
      rhoCutOrderParallel
        [rhoCutOrderWrappedDrop (.fvar "a"),
          rhoCutOrderWrappedDrop (.fvar "0")] := by
  calc
    (rhoCIGSLT.costNormalizeOpen rhoCutOrderLeft).1 =
        rhoCutOrderLeftElaboration.normalizeErasure.1 :=
      congrArg (fun term => term.1)
        (CostOpenElaboration.normalizeErasure_eq_costNormalizeOpen
          CostCanonicalLaws.rho_compactCostNormalizationCoherent
          rhoCutOrderLeftElaboration).symm
    _ = _ := by
      change rhoCutOrderLeftTree.normalize.pattern = _
      exact rhoCutOrderLeftTree_normalize

private theorem rhoCutOrderRight_costNormalizeOpen_pattern :
    (rhoCIGSLT.costNormalizeOpen rhoCutOrderRight).1 =
      rhoCutOrderRightPattern := by
  calc
    (rhoCIGSLT.costNormalizeOpen rhoCutOrderRight).1 =
        rhoCutOrderRightElaboration.normalizeErasure.1 :=
      congrArg (fun term => term.1)
        (CostOpenElaboration.normalizeErasure_eq_costNormalizeOpen
          CostCanonicalLaws.rho_compactCostNormalizationCoherent
          rhoCutOrderRightElaboration).symm
    _ = _ := by
      change rhoCutOrderRightTree.normalize.pattern = _
      exact rhoCutOrderRightTree_normalize

private theorem rhoCutOrder_normalPatterns_ne :
    rhoCutOrderParallel
        [rhoCutOrderWrappedDrop (.fvar "a"),
          rhoCutOrderWrappedDrop (.fvar "0")] ≠
      rhoCutOrderRightPattern := by
  simp [rhoCutOrderRightPattern, rhoCutOrderParallel,
    rhoCutOrderWrappedDrop]

/-- Child-first compact normalization distinguishes the two endpoints of the
authored rho Cost generator edge.  The enclosing wrapped region sorts its
boundary placeholder after `a`; restoring the normalized child replaces that
placeholder by `0` without re-sorting the parent. -/
theorem rhoCutOrder_costNormalizeOpen_ne :
    rhoCIGSLT.costNormalizeOpen rhoCutOrderLeft ≠
      rhoCIGSLT.costNormalizeOpen rhoCutOrderRight := by
  intro equality
  apply rhoCutOrder_normalPatterns_ne
  rw [← rhoCutOrderLeft_costNormalizeOpen_pattern,
    ← rhoCutOrderRight_costNormalizeOpen_pattern]
  exact congrArg (fun term => term.1) equality

/-- Exact compact generator invariance is false even for pure rho. -/
theorem not_rho_costOpenGeneratorInvariant :
    ¬ CostOpenGeneratorInvariant rhoCIGSLT := by
  intro invariant
  exact rhoCutOrder_costNormalizeOpen_ne (invariant rhoCutOrder_generator)

/-- The proof-relevant left decomposition used by the exactness
counterexample.  Exposing the witness lets successor normalizers demonstrate
that they repair this specific failure without re-running the planner inside
the regression proof. -/
noncomputable def rhoCutOrderLeftElaborationWitness :
    CostOpenElaboration rhoCIGSLT rhoCutOrderLeft :=
  ⟨rhoCutOrderLeftTree⟩

/-- The proof-relevant right decomposition used by the exactness
counterexample. -/
def rhoCutOrderRightElaborationWitness :
    CostOpenElaboration rhoCIGSLT rhoCutOrderRight :=
  ⟨rhoCutOrderRightTree⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
