import Mettapedia.GSLT.LanguageDef.CostRegionTree
import Mettapedia.GSLT.LanguageDef.CostRegionNormalization
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.EquationSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Exact Cost canonical laws for pure rho

This module discharges the selected-colour typed unary laws and compact
decomposition coherence needed on the way to placing the sole authored
pure-rho `LanguageDef` in the exact cost layer object domain.  Structural
properties are kept separate from the remaining contextual open-section
laws: finite candidate uniqueness is a decidable sufficient criterion, while
normalization soundness is stated through the authored equation relation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CostStaticRegionNode
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

private theorem optionSingletonList_length_le_one {α : Type}
    (candidate : Option α) :
    (match candidate with | none => [] | some value => [value]).length ≤ 1 := by
  cases candidate <;> simp

private theorem ifSingletonList_length_le_one {α : Type}
    (condition : Prop) [Decidable condition] (candidate : α) :
    (if condition then [candidate] else []).length ≤ 1 := by
  by_cases condition <;> simp_all

private theorem rhoCIGSLT_reflectionProfile_eq :
    rhoCIGSLT.reflection.1 = rhoReflectionProfile := by
  rfl

private theorem rhoReflectivePresentation_mem_source :
    rhoReflectivePresentation.toReflectivePresentationDecl ∈
      rhoCIGSLT.reflection.1.presentations := by
  rw [rhoCIGSLT_reflectionProfile_eq]
  simp [rhoReflectionProfile]

/-! ## Generated reflective substitution boundary -/

/-- Every constructor returning either generated copy of rho's name sort is
an authored quotation boundary of the generated Cost language.  The proof
uses intrinsic declaration identity: base and wrapped `NQuote` are the only
possible cases, while the fixed Cost apparatus inhabits disjoint reserved
sorts. -/
theorem rho_costReflectiveNameResultsQuoted :
    ReflectiveNameResultsQuoted (profile := rhoCIGSLT.costWholeReflectionProfile) rhoCIGSLT.costWholeLanguage := by
  intro declaration declarationMembership rule ruleMembership categoryEquality
  obtain ⟨color, sourceDeclaration, sourceMembership, rfl⟩ :=
    (mem_costStaticReflectivePresentations_iff_exists_source rhoCIGSLT).1
      declarationMembership
  have sourceDeclarationEq :
      sourceDeclaration =
        rhoReflectivePresentation.toReflectivePresentationDecl := by
    change (sourceDeclaration ∈ rhoReflectionProfile.presentations) at sourceMembership
    simpa [rhoReflectionProfile] using sourceMembership
  subst sourceDeclaration
  have interactingName :
      rhoCIGSLT.theory.presentation.interactingSort.1.name = "Proc" := by
    rfl
  have declarationNameSort :
      (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).nameSort =
        costBaseSortName "Name" := by
    cases color <;>
      simp [costStaticReflectivePresentationDecl_eq_map,
        mapReflectivePresentation, CostStaticColor.symbols, costBaseStaticSymbols,
        costBaseLanguageDefSymbolMap, costWrappedStaticSymbols,
        rhoReflectivePresentation, interactingName,
        show "Name" ≠ "Proc" by decide]
  have ruleCategoryBase : rule.category = costBaseSortName "Name" :=
    categoryEquality.trans declarationNameSort
  have coreMembership : rule ∈ rhoCIGSLT.costCoreLanguage.terms := by
    simpa only [rhoCIGSLT.costWholeLanguage_terms] using ruleMembership
  obtain ⟨constructor, rfl⟩ :=
    rhoCIGSLT.exists_declaredCostConstructor_of_mem rule coreMembership
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base sourceConstructor =>
      rcases sourceConstructor with ⟨sourceRule, sourceRuleMembership⟩
      have sourceCategory : sourceRule.category = "Name" := by
        apply costBaseSortName_injective
        simpa [CIGSLT.materializeDeclaredCostConstructor,
          costBaseConstructor] using ruleCategoryBase
      obtain ⟨sourceLabel, sourceNotBare⟩ :=
        EquationSubstitution.rho_reflectiveNameResultSealed
          rhoReflectivePresentation.toReflectivePresentationDecl
          sourceMembership sourceRule sourceRuleMembership sourceCategory
      refine ⟨?_, ?_⟩
      · simp only [ReflectiveContextSupport.isQuoteConstructor,
          List.any_eq_true]
        refine ⟨costStaticReflectivePresentationDecl rhoCIGSLT .base
          rhoReflectivePresentation.toReflectivePresentationDecl,
          ?_, ?_⟩
        · simpa only [rhoCIGSLT.costWholeReflectionProfile_presentations]
            using costStaticReflectivePresentationDecl_mem rhoCIGSLT .base
              rhoReflectivePresentation.toReflectivePresentationDecl
                sourceMembership
        · simp [CIGSLT.materializeDeclaredCostConstructor,
            costBaseConstructor, costStaticReflectivePresentationDecl,
            costBaseReflectivePresentationDecl, mapReflectivePresentation,
            costBaseStaticReflectiveSymbols, costBaseStaticSymbols,
            costBaseLanguageDefSymbolMap, sourceLabel]
      · intro targetBare
        exact sourceNotBare
          ((usesBareCollection_costBaseConstructor_iff rhoCIGSLT.cut
            sourceRule).mp (by
              simpa [CIGSLT.materializeDeclaredCostConstructor] using
                targetBare))
  | wrapped sourceConstructor =>
      rcases sourceConstructor with ⟨sourceRule, sourceRuleMembership⟩
      have sourceCategory : sourceRule.category = "Name" := by
        by_cases interacting : sourceRule.category = "Proc"
        · have impossible : costWrappedSortName = costBaseSortName "Name" := by
            simpa [CIGSLT.materializeDeclaredCostConstructor,
              costWrappedConstructor, interacting, interactingName] using
                ruleCategoryBase
          exact False.elim
            (costBaseSortName_ne_wrapped "Name" impossible.symm)
        · apply costBaseSortName_injective
          simpa [CIGSLT.materializeDeclaredCostConstructor,
            costWrappedConstructor, interacting, interactingName] using
              ruleCategoryBase
      obtain ⟨sourceLabel, sourceNotBare⟩ :=
        EquationSubstitution.rho_reflectiveNameResultSealed
          rhoReflectivePresentation.toReflectivePresentationDecl
          sourceMembership sourceRule sourceRuleMembership sourceCategory
      refine ⟨?_, ?_⟩
      · simp only [ReflectiveContextSupport.isQuoteConstructor,
          List.any_eq_true]
        refine ⟨costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation.toReflectivePresentationDecl,
          ?_, ?_⟩
        · simpa only [rhoCIGSLT.costWholeReflectionProfile_presentations]
            using costStaticReflectivePresentationDecl_mem rhoCIGSLT .wrapped
              rhoReflectivePresentation.toReflectivePresentationDecl
                sourceMembership
        · simp [CIGSLT.materializeDeclaredCostConstructor,
            costWrappedConstructor, costStaticReflectivePresentationDecl,
            costWrappedReflectivePresentationDecl, mapReflectivePresentation,
            costWrappedStaticReflectiveSymbols, costWrappedStaticSymbols,
            sourceLabel]
      · intro targetBare
        exact sourceNotBare
          ((usesBareCollection_costWrappedConstructor_iff sourceRule).mp (by
            simpa [CIGSLT.materializeDeclaredCostConstructor] using
              targetBare))
  | apparatus kind =>
      cases kind with
      | signatureUnit | signatureProduct =>
          exact False.elim (costBaseSortName_ne_apparatus "Name" "signature"
            (by simpa [CIGSLT.materializeDeclaredCostConstructor,
              CostApparatusConstructor.grammarRule,
              costSignatureUnitConstructor, costSignatureProductConstructor,
              costSignatureSortName] using ruleCategoryBase.symm))
      | signed | funding | contact =>
          exact False.elim (costBaseSortName_ne_wrapped "Name"
            (by simpa [CIGSLT.materializeDeclaredCostConstructor,
              CostApparatusConstructor.grammarRule, costSignedConstructor,
              costFundingConstructor, costContactConstructor]
                using ruleCategoryBase.symm))
      | tokenStackEmpty | tokenStackCons =>
          exact False.elim (costBaseSortName_ne_apparatus "Name" "token-stack"
            (by simpa [CIGSLT.materializeDeclaredCostConstructor,
              CostApparatusConstructor.grammarRule,
              costTokenStackEmptyConstructor, costTokenStackConsConstructor,
              costTokenStackSortName] using ruleCategoryBase.symm))

/-- No collection node inhabits either generated reflective name fibre of
rho Cost.  A raw collection has a collection type, while a collection at a
base type must use an authored bare-collection rule.  The generated
name-result classification rules out the latter: every name-resulting rule is
a quotation constructor and is not bare.

This is the typed guard needed when Quote/Drop exposes its name payload.  In
particular, a process parallel bag cannot be exposed into that name fibre,
even though an untyped keyed canonicalizer can exhibit exactly that shape. -/
theorem rho_no_collection_at_reflectiveNameSort
    (declaration : ReflectivePresentationDecl)
    (declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {collectionType : CollType} {elements : List Pattern}
    {rest : Option String} :
    ¬ HasType rhoCIGSLT.costWholeLanguage free bound
      (.collection collectionType elements rest) (.base declaration.nameSort) := by
  intro typed
  rcases hasType_collection_inversion typed with
    ⟨elementType, impossible, elementsTyped⟩ |
      ⟨rule, parameterName, elementType, membership, parameterShape,
        resultType, elementsTyped⟩
  · cases impossible
  · have categoryEquality : rule.category = declaration.nameSort :=
      (TypeExpr.base.inj resultType).symm
    have notBare :=
      (rho_costReflectiveNameResultsQuoted declaration declarationMembership
        rule membership categoryEquality).2
    exact notBare ⟨parameterName, collectionType, elementType,
      parameterShape⟩

/-- The selected Drop constructor in either generated rho Cost colour is an
ordinary constructor, never a quotation boundary. -/
theorem rho_costStatic_drop_isOrdinary (color : CostStaticColor) :
    ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).dropConstructor = false := by
  rw [show
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
      ).dropConstructor =
        (color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.dropConstructor by
    simp [costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation]]
  rw [reflectiveIsQuoteConstructor_mapCostStatic]
  rw [rhoCIGSLT_reflectionProfile_eq]
  simp [rhoReflectionProfile, ReflectiveContextSupport.isQuoteConstructor,
    rhoReflectivePresentation]

/-- In either generated rho Cost colour, a typed Quote/Drop redex carries a
payload in that declaration's exact reflective name fibre.  The support
witness is returned below the quote reset, at visible depth zero.

Together with `rho_no_collection_at_reflectiveNameSort`, this rules out the
untyped counterexample in which Quote/Drop exposes a process parallel bag and
an enclosing keyed collection re-sorts it at another depth. -/
theorem rho_costStatic_quoteDrop_inner_typed
    (color : CostStaticColor)
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    {inner : Pattern} {type : TypeExpr}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [inner]]) type)
    (safe : typed.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    ∃ innerTyped : HasType rhoCIGSLT.costWholeLanguage free bound inner
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).nameSort),
      innerTyped.ReflectiveSupportSafeAt rhoCIGSLT.costWholeReflectionProfile
        support [] binderImage := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        rhoReflectivePresentation_mem_source
  obtain ⟨argument, argumentTyped, argumentsShape, argumentSafe⟩ :=
    typed.selectedQuoteArgument rhoCIGSLT.costWholeLanguage_validate
      rhoCIGSLT.costWholeReflectionProfile_validate declarationMembership safe
  have argumentEquality :
      .apply declaration.dropConstructor [inner] = argument := by
    simpa [declaration] using (List.cons.inj argumentsShape).1
  subst argument
  obtain ⟨payload, payloadTyped, payloadShape, payloadSafe⟩ :=
    argumentTyped.selectedOrdinaryDropArgument
      rhoCIGSLT.costWholeLanguage_validate
      rhoCIGSLT.costWholeReflectionProfile_validate declarationMembership
      (by simpa [declaration] using rho_costStatic_drop_isOrdinary color)
      argumentSafe
  have payloadEquality : inner = payload := by
    simpa using (List.cons.inj payloadShape).1
  subst payload
  exact ⟨payloadTyped, payloadSafe⟩

/-! ### Why the generated law is static-fiber scoped

The raw rho parallel collection tag is intentionally shared by the two Cost
colours, while the two process sorts and their unit constructors are distinct.
Consequently a canonicalizer for one colour is not type preserving on an
arbitrary term of the other colour.  The following compact witness prevents
the cost layer laws from being accidentally strengthened to all mixed-colour raw
terms; the actual region normalizer invokes substitution only on one mapped
static fibre at a time. -/

private def rhoCostMixedColorName : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.collection .hashBag [] none]

private def rhoCostMixedColorDrop : Pattern :=
  .apply (costWrappedConstructorName "PDrop") [rhoCostMixedColorName]

private def rhoCostMixedColorCanonicalName : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PZero") []]

private def rhoCostMixedColorCanonicalDrop : Pattern :=
  .apply (costWrappedConstructorName "PDrop")
    [rhoCostMixedColorCanonicalName]

private theorem rhoCostWrappedZero_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (.apply (costWrappedConstructorName "PZero") [])
      (.base costWrappedSortName) := by
  exact checkHasType_sound (by decide)

private theorem rhoCostMixedColorDrop_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      rhoCostMixedColorDrop (.base costWrappedSortName) := by
  exact checkHasType_sound (by decide)

private theorem rhoCostMixedColorDrop_supportSafe :
    rhoCostMixedColorDrop_typed.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile (fun _ => []) [] :=
  rhoCostMixedColorDrop_typed.reflectiveSupportSafeAt_empty []

private theorem rhoCostMixedColorDrop_object :
    isObjectPattern rhoCostMixedColorDrop = true := by
  decide

private theorem rhoCostMixedColorDrop_canonicalize :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rhoCostMixedColorDrop =
      rhoCostMixedColorCanonicalDrop := by
  simp [rhoCostMixedColorDrop, rhoCostMixedColorName,
    rhoCostMixedColorCanonicalName, rhoCostMixedColorCanonicalDrop,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    costStaticReflectivePresentationDecl,
    costWrappedReflectivePresentationDecl, mapReflectivePresentation,
    costWrappedStaticReflectiveSymbols, costWrappedStaticSymbols,
    rhoReflectivePresentation, rhoCIGSLT,
    rhoIGSLT, rhoInteractivePresentation, rhoCalc, TypeDecl.plain,
    costBaseConstructorName, costBaseConstructorTag,
    costWrappedConstructorName, costWrappedConstructorTag,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns]

private theorem rhoCostMixedColorCanonicalName_not_typed :
    ¬ HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      rhoCostMixedColorCanonicalName (.base (costBaseSortName "Name")) := by
  change ¬ HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
    (.apply (costBaseConstructorName "NQuote")
      [.apply (costWrappedConstructorName "PZero") []])
    (.base (costBaseSortName "Name"))
  intro typed
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl
        rhoReflectivePresentation_mem_source
  have typed' : HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (.apply declaration.quoteConstructor
        [.apply (costWrappedConstructorName "PZero") []])
      (.base (costBaseSortName "Name")) := by
    simpa [declaration, costStaticReflectivePresentationDecl,
      costBaseReflectivePresentationDecl, mapReflectivePresentation,
      costBaseStaticSymbols, costBaseLanguageDefSymbolMap,
      CostStaticColor.symbols, CostStaticColor.constructorTag,
      rhoReflectivePresentation] using typed
  obtain ⟨argument, argumentTyped, argumentsShape, _argumentSafe⟩ :=
    typed'.selectedQuoteArgument rhoCIGSLT.costWholeLanguage_validate
      rhoCIGSLT.costWholeReflectionProfile_validate declarationMembership
      (typed'.reflectiveSupportSafeAt_empty [])
  have argumentEquality :
      .apply (costWrappedConstructorName "PZero") [] = argument := by
    simpa using argumentsShape
  subst argument
  have baseTyped : HasType rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty []
      (.apply (costWrappedConstructorName "PZero") [])
      (.base (costBaseSortName "Proc")) := by
    simpa [declaration, costStaticReflectivePresentationDecl,
      costBaseReflectivePresentationDecl, mapReflectivePresentation,
      costBaseStaticSymbols, costBaseLanguageDefSymbolMap,
      CostStaticColor.symbols, CostStaticColor.constructorTag,
      rhoReflectivePresentation] using argumentTyped
  have typeEquality := HasType.apply_type_unique_of_validate_eq_nil
    rhoCIGSLT.costWholeLanguage_validate baseTyped rhoCostWrappedZero_typed
  have sortEquality : costBaseSortName "Proc" = costWrappedSortName :=
    TypeExpr.base.inj typeEquality
  exact costBaseSortName_ne_wrapped "Proc" sortEquality

private theorem rhoCostMixedColorCanonicalDrop_not_typed :
    ¬ HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      rhoCostMixedColorCanonicalDrop (.base costWrappedSortName) := by
  intro typed
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership :
      declaration ∈ rhoCIGSLT.costWholeReflectionProfile.presentations := by
    change declaration ∈ rhoCIGSLT.costStaticReflectivePresentations
    apply costStaticReflectivePresentationDecl_mem
    exact .head _
  have dropOrdinary :
      ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile declaration.dropConstructor = false := by
    simpa [declaration] using rho_costStatic_drop_isOrdinary .wrapped
  obtain ⟨argument, argumentTyped, argumentsShape, _argumentSafe⟩ :=
    typed.selectedOrdinaryDropArgument
      rhoCIGSLT.costWholeLanguage_validate
      rhoCIGSLT.costWholeReflectionProfile_validate declarationMembership
      dropOrdinary (typed.reflectiveSupportSafeAt_empty [])
  have argumentEquality : argument = rhoCostMixedColorCanonicalName := by
    simpa [rhoCostMixedColorCanonicalDrop] using
      (congrArg List.head? argumentsShape).symm
  subst argument
  have declarationNameSort :
      declaration.nameSort = costBaseSortName "Name" := by
    simp [declaration, mapReflectivePresentation,
      CostStaticColor.symbols, costWrappedStaticSymbols,
      rhoReflectivePresentation, rhoCIGSLT, rhoIGSLT,
      rhoInteractivePresentation, rhoValidatedLanguageDef, rhoCalc,
      TypeDecl.plain, show "Name" ≠ "Proc" by decide]
  apply rhoCostMixedColorCanonicalName_not_typed
  simpa only [declarationNameSort] using argumentTyped

/-- Negative canary: reflective substitution stability of the generated Cost
language cannot honestly be required on every mixed-colour raw term.  A
wrapped Drop may contain a base Quote whose empty base parallel body is
collapsed by the wrapped canonicalizer to the wrapped unit.  The resulting
name is not sorted in the original base quotation fibre. -/
theorem rho_costReflectiveDropCanonicalSupportStable_not :
    ¬ ReflectiveDropCanonicalSupportStable (profile := rhoCIGSLT.costWholeReflectionProfile) rhoCIGSLT.costWholeLanguage := by
  intro stable
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT .wrapped
        rhoReflectivePresentation.toReflectivePresentationDecl
        rhoReflectivePresentation_mem_source
  have exposed := stable declaration declarationMembership
    rhoCostMixedColorDrop_typed rhoCostMixedColorDrop_supportSafe
      rhoCostMixedColorDrop_object (by
        have dropConstructor : declaration.dropConstructor =
            costWrappedConstructorName "PDrop" := by
          simp [declaration, costStaticReflectivePresentationDecl_eq_map,
            mapReflectivePresentation, CostStaticColor.reflectiveSymbols,
            costWrappedStaticReflectiveSymbols, costWrappedStaticSymbols,
            rhoReflectivePresentation]
        rw [dropConstructor]
        simpa only [rhoCostMixedColorCanonicalDrop] using
          rhoCostMixedColorDrop_canonicalize)
  rcases exposed with ⟨nameTyped, _nameSafe, _nameObject⟩
  exact rhoCostMixedColorCanonicalName_not_typed nameTyped

/-- Negative canary: the raw generated Cost equation relation is not globally
fiber-stable.  A well-sorted mixed-colour Drop is reflectively related to a
canonicalized endpoint whose base quotation contains a wrapped process.
The region compiler therefore must prove typed soundness for its selected
paths rather than assume that every raw generated edge preserves every
possible typing fiber. -/
theorem rho_costOpenEquationFiberStable_not :
    ¬ ReflectiveEquationSemantics.ReflectiveOpenEquationFiberStable
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
        rhoCIGSLT.costWholeLanguage := by
  intro stable
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership :
      declaration ∈ rhoCIGSLT.costWholeReflectionProfile.presentations := by
    change declaration ∈ rhoCIGSLT.costStaticReflectivePresentations
    apply costStaticReflectivePresentationDecl_mem
    exact .head _
  have representatives :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          rhoCostMixedColorDrop =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          rhoCostMixedColorCanonicalDrop := by
    have normalized :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          rhoCostMixedColorDrop = rhoCostMixedColorCanonicalDrop := by
      simpa [declaration] using rhoCostMixedColorDrop_canonicalize
    calc
      _ = rhoCostMixedColorCanonicalDrop := normalized
      _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          rhoCostMixedColorDrop := normalized.symm
      _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
            rhoCostMixedColorDrop) :=
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_idempotent
          declaration rhoCostMixedColorDrop).symm
      _ = _ := congrArg
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration)
        normalized
  have generator :
      ReflectiveEquationSemantics.ReflectiveEquationContextStep rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage rhoCostMixedColorDrop
          rhoCostMixedColorCanonicalDrop := by
    exact ReflectiveEquationSemantics.ReflectiveEquationContextStep.reflectiveInContext
      (base := defaultBasePremises) (.hole) declarationMembership
        representatives
  have leftWellSorted :
      ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        FreeTypeContext.empty [] (.base costWrappedSortName)
          rhoCostMixedColorDrop :=
    ⟨checkOpenPatternWellSorted_sound (by decide), by
      intro declaration _membership
      simp [rhoCostMixedColorDrop, rhoCostMixedColorName,
        binderSafeAt, binderSafeListAt]⟩
  have rightWellSorted := (stable generator).mp leftWellSorted
  exact rhoCostMixedColorCanonicalDrop_not_typed rightWellSorted.1.1

/-! ## Same-colour mapped equation action -/

/-- The three reflective constructors introduced by rho canonicalization all
belong to the continuation fragment admitted by the selected static action. -/
private theorem rho_costReflectiveConstructorsAllowed :
    ReflectiveConstructorsAllowed
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels)
      rhoReflectivePresentation := by
  constructor
  · let constructor : StructuralMorphism.DeclaredConstructor
        rhoIGSLT.presentation.presentation :=
      ⟨rhoCalc.terms[2], List.getElem_mem (by simp [rhoCalc])⟩
    change constructor.1.label ∈ rhoContinuationRetyping.wrappedLabels
    apply (rhoContinuationRetyping.mem_wrappedLabels_iff constructor).2
    rw [rhoContinuationRetyping.mem_wrappedConstructors_iff]
    constructor <;> decide
  · let constructor : StructuralMorphism.DeclaredConstructor
        rhoIGSLT.presentation.presentation :=
      ⟨rhoCalc.terms[1], List.getElem_mem (by simp [rhoCalc])⟩
    change constructor.1.label ∈ rhoContinuationRetyping.wrappedLabels
    apply (rhoContinuationRetyping.mem_wrappedLabels_iff constructor).2
    rw [rhoContinuationRetyping.mem_wrappedConstructors_iff]
    constructor <;> decide
  · let constructor : StructuralMorphism.DeclaredConstructor
        rhoIGSLT.presentation.presentation :=
      ⟨rhoCalc.terms[0], List.getElem_mem (by simp [rhoCalc])⟩
    change constructor.1.label ∈ rhoContinuationRetyping.wrappedLabels
    apply (rhoContinuationRetyping.mem_wrappedLabels_iff constructor).2
    rw [rhoContinuationRetyping.mem_wrappedConstructors_iff]
    constructor <;> decide

/-- The local form of the same-colour static action.  `inner` counts binders
introduced inside the source skeleton, while `available` is the independently
tracked reflective-substitution context (and is reset below quotation). -/
def rhoCostStaticActionAt
    {color : CostStaticColor}
    {assignmentFree targetFree : FreeTypeContext}
    {assignmentSupport : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    (assignment : SupportedOpenAssignment rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      assignmentFree targetFree assignmentSupport)
    (inner available : List TypeExpr) (pattern : Pattern) : Pattern :=
  ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
    assignmentSupport assignment.assignment available.length
      (thinning.thickenAmbientBVars inner.length
        (mapPattern (color.symbols rhoCIGSLT) pattern))

/-- A source rho name mapped into one selected Cost colour, reinserted through
an arbitrary ambient thinning, and then restored by an arbitrary supported
Cost assignment has the exact selected generated Quote/Drop representative.
The assignment values may use either colour; only the surrounding equation
skeleton is required to remain monochromatic. -/
private theorem rho_costStatic_quoteDrop_action_canonicalize_eq
    {color : CostStaticColor}
    {free targetFree : FreeTypeContext}
    {support : ContextSupport.Support}
    {sourceBound targetBound inner : List TypeExpr}
    {name : Pattern} {resultType : TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    (assignment : SupportedOpenAssignment rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      (free.map (color.symbols rhoCIGSLT)) targetFree support)
    (typed : HasType rhoCalc free (inner ++ sourceBound) name resultType)
    (resultType_eq : resultType = TypeExpr.name)
    (safeAtZero : typed.ReflectiveSupportSafeAt rhoReflectionProfile support []
      (mapTypeExpr (color.symbols rhoCIGSLT)))
    (supported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) name)
    (object : isObjectPattern name = true)
    (availableDepth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
          support assignment.assignment availableDepth
          (thinning.thickenAmbientBVars inner.length
            (mapPattern (color.symbols rhoCIGSLT)
              (.apply "NQuote" [.apply "PDrop" [name]])))) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
          support assignment.assignment availableDepth
          (thinning.thickenAmbientBVars inner.length
            (mapPattern (color.symbols rhoCIGSLT) name))) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership :
      declaration ∈ rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        rhoReflectivePresentation_mem_source
  have quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor := by
    cases color <;>
      simp [declaration, mapReflectivePresentation, rhoReflectivePresentation]
  obtain ⟨mappedTyped, mappedSafe⟩ :=
    safeAtZero.mapCostStatic rhoCIGSLT color supported
  have mappedTypedSafe :
      ∃ mappedTyped' : HasType rhoCIGSLT.costWholeLanguage
          (free.map (color.symbols rhoCIGSLT))
          (inner.map (mapTypeExpr (color.symbols rhoCIGSLT)) ++
            sourceBound.map (mapTypeExpr (color.symbols rhoCIGSLT)))
          (mapPattern (color.symbols rhoCIGSLT) name)
          (mapTypeExpr (color.symbols rhoCIGSLT) resultType),
        mappedTyped'.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support [] := by
    have raw :
        ∃ mappedTyped' : HasType rhoCIGSLT.costWholeLanguage
            (free.map (color.symbols rhoCIGSLT))
            ((inner ++ sourceBound).map
              (mapTypeExpr (color.symbols rhoCIGSLT)))
            (mapPattern (color.symbols rhoCIGSLT) name)
            (mapTypeExpr (color.symbols rhoCIGSLT) resultType),
          mappedTyped'.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support [] :=
      ⟨mappedTyped, mappedSafe⟩
    simpa only [List.map_append] using raw
  obtain ⟨mappedTyped, mappedSafe⟩ := mappedTypedSafe
  let thickenedTyped := mappedTyped.thickenAmbientBVars
    (source := rhoCIGSLT) (color := color)
      (inner := inner.map (mapTypeExpr (color.symbols rhoCIGSLT))) thinning
  have thickenedSafe : thickenedTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support [] :=
    WellSorted.HasType.ReflectiveSupportSafeAt.thickenAmbientBVars
      (source := rhoCIGSLT) (color := color)
      (inner := inner.map (mapTypeExpr (color.symbols rhoCIGSLT)))
      mappedSafe thinning
  have thickenedObject :
      isObjectPattern
          (thinning.thickenAmbientBVars inner.length
            (mapPattern (color.symbols rhoCIGSLT) name)) = true := by
    rw [CostStaticBinderThinning.isObjectPattern_thickenAmbientBVars,
      WellSorted.isObjectPattern_mapPattern]
    exact object
  have cancellation :=
    quoteDrop_substituteAt_canonicalize_eq_of_resultsQuoted
    rho_costReflectiveNameResultsQuoted assignment declaration
      declarationMembership quoteNeDrop thickenedTyped
      (by
        subst resultType
        cases color <;>
          rfl)
      thickenedSafe.castTyping
      (by simpa only [List.length_map] using thickenedObject) availableDepth
  simpa only [declaration, costStaticReflectivePresentationDecl_eq_map,
    mapReflectivePresentation, mapPattern, mapPatternList_eq_map,
    CostStaticColor.reflectiveSymbols_constructor,
    CostStaticBinderThinning.thickenAmbientBVars, List.length_map,
    List.map_cons, List.map_nil, rhoReflectivePresentation]
    using cancellation

/-- The exact selected representative above is one generated reflective
Quote/Drop generator. -/
private theorem rho_costStatic_quoteDrop_action_step
    {color : CostStaticColor}
    {free targetFree : FreeTypeContext}
    {support : ContextSupport.Support}
    {sourceBound targetBound inner : List TypeExpr}
    {name : Pattern} {resultType : TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    (assignment : SupportedOpenAssignment rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      (free.map (color.symbols rhoCIGSLT)) targetFree support)
    (typed : HasType rhoCalc free (inner ++ sourceBound) name resultType)
    (resultType_eq : resultType = TypeExpr.name)
    (safeAtZero : typed.ReflectiveSupportSafeAt rhoReflectionProfile support []
      (mapTypeExpr (color.symbols rhoCIGSLT)))
    (supported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) name)
    (object : isObjectPattern name = true)
    (availableDepth : Nat) :
    ReflectiveEquationSemantics.ReflectiveEquationContextStep rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage
      (ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
        support assignment.assignment availableDepth
        (thinning.thickenAmbientBVars inner.length
          (mapPattern (color.symbols rhoCIGSLT)
            (.apply "NQuote" [.apply "PDrop" [name]]))))
      (ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
        support assignment.assignment availableDepth
        (thinning.thickenAmbientBVars inner.length
          (mapPattern (color.symbols rhoCIGSLT) name))) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership :
      declaration ∈ rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        rhoReflectivePresentation_mem_source
  apply ReflectiveEquationSemantics.ReflectiveEquationContextStep.reflectiveInContext .hole
    declarationMembership
  simpa only [declaration] using
    rho_costStatic_quoteDrop_action_canonicalize_eq thinning assignment typed
      resultType_eq safeAtZero supported object availableDepth

/-- Closure-level wrapper around the direct selected-colour Quote/Drop
generator. -/
private theorem rho_costStatic_quoteDrop_action
    {color : CostStaticColor}
    {free targetFree : FreeTypeContext}
    {support : ContextSupport.Support}
    {sourceBound targetBound inner : List TypeExpr}
    {name : Pattern} {resultType : TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    (assignment : SupportedOpenAssignment rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      (free.map (color.symbols rhoCIGSLT)) targetFree support)
    (typed : HasType rhoCalc free (inner ++ sourceBound) name resultType)
    (resultType_eq : resultType = TypeExpr.name)
    (safeAtZero : typed.ReflectiveSupportSafeAt rhoReflectionProfile support []
      (mapTypeExpr (color.symbols rhoCIGSLT)))
    (supported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) name)
    (object : isObjectPattern name = true)
    (availableDepth : Nat) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage
      (ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
        support assignment.assignment availableDepth
        (thinning.thickenAmbientBVars inner.length
          (mapPattern (color.symbols rhoCIGSLT)
            (.apply "NQuote" [.apply "PDrop" [name]]))))
      (ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
        support assignment.assignment availableDepth
        (thinning.thickenAmbientBVars inner.length
          (mapPattern (color.symbols rhoCIGSLT) name))) := by
  exact Relation.EqvGen.rel _ _
    (rho_costStatic_quoteDrop_action_step thinning assignment typed
      resultType_eq safeAtZero supported object availableDepth)

private theorem rhoCostEquationEquiv_trans {left middle right : Pattern}
    (first : ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left middle)
    (second : ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage middle right) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right :=
  Relation.EqvGen.trans _ _ _ first second

private theorem rho_finishNormalizeReflectiveApply_quote_eq_of_not_drop
    {argument : Pattern}
    (notDrop : ¬ ∃ name,
      argument = .apply rhoReflectivePresentation.dropConstructor [name]) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        rhoReflectivePresentation rhoReflectivePresentation.quoteConstructor
          [argument] =
      .apply rhoReflectivePresentation.quoteConstructor [argument] := by
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
  simp only [beq_self_eq_true, if_true]
  cases argument with
  | apply constructor arguments =>
      cases arguments with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil =>
              by_cases dropLabel :
                  constructor = rhoReflectivePresentation.dropConstructor
              · subst constructor
                exact False.elim (notDrop ⟨first, rfl⟩)
              · simp [dropLabel]
          | cons second tail => rfl
  | bvar index => rfl
  | fvar name => rfl
  | lambda binder body => rfl
  | multiLambda arity binders body => rfl
  | subst body replacement => rfl
  | collection collectionType elements rest => rfl

/-- Re-canonicalizing in the selected generated colour absorbs source-rho
canonicalization before the typed boundary action.  This is stronger than a
raw target equivalence: it retains the exact reflective declaration that
justifies the eventual one-edge typed path. -/
private theorem rhoCostStaticActionAt_canonicalize_eq
    {color : CostStaticColor}
    {free assignmentFree targetFree : FreeTypeContext}
    {support assignmentSupport : ContextSupport.Support}
    {sourceBound targetBound inner available : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    (assignment : SupportedOpenAssignment rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      assignmentFree targetFree assignmentSupport)
    (freeContext : free.map (color.symbols rhoCIGSLT) = assignmentFree)
    (reflectiveSupport : support = assignmentSupport)
    (typed : HasType rhoCalc free (inner ++ sourceBound) pattern type)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available
      (mapTypeExpr (color.symbols rhoCIGSLT)))
    (supported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) pattern)
    (object : isObjectPattern pattern = true) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (rhoCostStaticActionAt thinning assignment inner available pattern) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (rhoCostStaticActionAt thinning assignment inner available
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
            rhoReflectivePresentation pattern)) := by
  subst assignmentFree
  subst assignmentSupport
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have sourceMembership :
      rhoReflectivePresentation.toReflectivePresentationDecl ∈
        rhoReflectionProfile.presentations := by
    simp [rhoReflectionProfile]
  have targetQuoteStatus :
      ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
          ((color.symbols rhoCIGSLT).constructor
            rhoReflectivePresentation.quoteConstructor) = true := by
    rw [reflectiveIsQuoteConstructor_mapCostStatic]
    rw [rhoCIGSLT_reflectionProfile_eq]
    simp [rhoReflectionProfile, ReflectiveContextSupport.isQuoteConstructor,
      rhoReflectivePresentation]
  have targetDeclarationQuote : targetDeclaration.quoteConstructor =
      (color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor := by
    simp [targetDeclaration, mapReflectivePresentation]
  have targetQuoteStatusTag :
      ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
          (color.constructorTag ++
            rhoReflectivePresentation.quoteConstructor) = true := by
    rw [← CostStaticColor.symbols_constructor]
    exact targetQuoteStatus
  change
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize targetDeclaration
        (rhoCostStaticActionAt thinning assignment inner available pattern) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize targetDeclaration
        (rhoCostStaticActionAt thinning assignment inner available
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
            rhoReflectivePresentation pattern))
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType rhoCalc free bound pattern type)
      (currentAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        currentAvailable currentImage) =>
      ∀ (currentInner : List TypeExpr),
        bound = currentInner ++ sourceBound →
        currentImage = mapTypeExpr (color.symbols rhoCIGSLT) →
        ConstructorsWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) pattern →
        isObjectPattern pattern = true →
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
            targetDeclaration
            (rhoCostStaticActionAt thinning assignment currentInner
              currentAvailable pattern) =
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
            targetDeclaration
            (rhoCostStaticActionAt thinning assignment currentInner
              currentAvailable
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation pattern)))
    (motive_2 := fun {bound arguments parameters}
      (typed : ArgumentsHaveTypes rhoCalc free bound arguments parameters)
      (currentAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        currentAvailable currentImage) =>
      ∀ (currentInner : List TypeExpr),
        bound = currentInner ++ sourceBound →
        currentImage = mapTypeExpr (color.symbols rhoCIGSLT) →
        ConstructorListWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) arguments →
        isObjectPatternList arguments = true →
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
            targetDeclaration
            (arguments.map
              (rhoCostStaticActionAt thinning assignment currentInner
                currentAvailable)) =
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
            targetDeclaration
            ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              rhoReflectivePresentation arguments).map
                (rhoCostStaticActionAt thinning assignment currentInner
                  currentAvailable)))
    (motive_3 := fun {bound elements elementType}
      (typed : ElementsHaveType rhoCalc free bound elements elementType)
      (currentAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        currentAvailable currentImage) =>
      ∀ (currentInner : List TypeExpr),
        bound = currentInner ++ sourceBound →
        currentImage = mapTypeExpr (color.symbols rhoCIGSLT) →
        ConstructorListWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) elements →
        isObjectPatternList elements = true →
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
            targetDeclaration
            (elements.map
              (rhoCostStaticActionAt thinning assignment currentInner
                currentAvailable)) =
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
            targetDeclaration
            ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              rhoReflectivePresentation elements).map
                (rhoCostStaticActionAt thinning assignment currentInner
                  currentAvailable)))
    (by
      intro bound index resultType lookup currentAvailable currentImage
        currentInner boundEquality imageEquality resultSupported resultObject
      rfl)
    (by
      intro bound freeName resultType lookup currentAvailable currentImage shape
        currentInner boundEquality imageEquality resultSupported resultObject
      rfl)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        currentAvailable currentImage quoted argumentsSafe argumentsIH
        currentInner boundEquality imageEquality resultSupported resultObject
      have argumentsSupported : ConstructorListWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) arguments :=
        resultSupported.2
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using resultObject
      have selectedByQuote :
          rule.label = rhoReflectivePresentation.quoteConstructor := by
        unfold ReflectiveContextSupport.isQuoteConstructor at quoted
        rw [List.any_eq_true] at quoted
        obtain ⟨declaration, declarationMembership, quoteLabel⟩ := quoted
        have declarationEquality : declaration =
            rhoReflectivePresentation.toReflectivePresentationDecl := by
          simpa [rhoReflectionProfile] using declarationMembership
        subst declaration
        have quoteLabel' :
            rhoReflectivePresentation.quoteConstructor = rule.label := by
          simpa using quoteLabel
        exact quoteLabel'.symm
      obtain ⟨argument, argumentTyped, rfl, argumentSafe⟩ :=
        argumentsTyped.selectedQuoteArgument
          LanguageDefAdequacy.rhoCalc_validate
            rhoCalcValidatedReflective.admittedReflection.2 sourceMembership
            membership selectedByQuote
            argumentsSafe
      have argumentSupported : ConstructorsWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) argument :=
        argumentsSupported.1
      have argumentObject : isObjectPattern argument = true := by
        simpa [isObjectPatternList] using argumentsObject
      have argumentEquality :
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              targetDeclaration
              (rhoCostStaticActionAt thinning assignment currentInner []
                argument) =
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              targetDeclaration
              (rhoCostStaticActionAt thinning assignment currentInner []
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  rhoReflectivePresentation argument)) := by
        simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList]
          using argumentsIH currentInner boundEquality imageEquality
            argumentsSupported argumentsObject
      have quoteAction (payload : Pattern) :
          rhoCostStaticActionAt thinning assignment currentInner
              currentAvailable
              (.apply rhoReflectivePresentation.quoteConstructor [payload]) =
            .apply targetDeclaration.quoteConstructor
              [rhoCostStaticActionAt thinning assignment currentInner []
                payload] := by
        rw [targetDeclarationQuote]
        simp [rhoCostStaticActionAt,
          ReflectiveContextSupport.substituteAt,
          CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
          targetQuoteStatusTag]
      by_cases dropShape : ∃ name,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              rhoReflectivePresentation argument =
            .apply rhoReflectivePresentation.dropConstructor [name]
      · obtain ⟨name, canonicalEquality⟩ := dropShape
        obtain ⟨nameTyped, nameSafe, nameObject⟩ :=
          EquationSubstitution.rho_reflectiveDropCanonicalSupportStable
            rhoReflectivePresentation.toReflectivePresentationDecl
              sourceMembership argumentTyped argumentSafe argumentObject
                canonicalEquality
        have canonicalSupported : ConstructorsWithin
            (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels)
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              rhoReflectivePresentation argument) :=
          (constructorsWithin_canonicalize_iff rhoReflectivePresentation
            rho_costReflectiveConstructorsAllowed argument).2
              argumentSupported
        rw [canonicalEquality] at canonicalSupported
        have nameSupported : ConstructorsWithin
            (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) name :=
          canonicalSupported.2.1
        have nameTypedSafe :
            ∃ nameTyped' : HasType rhoCalc free
                (currentInner ++ sourceBound) name
                (.base rhoReflectivePresentation.nameSort),
              nameTyped'.ReflectiveSupportSafeAt rhoReflectionProfile support []
                (mapTypeExpr (color.symbols rhoCIGSLT)) := by
          rw [← boundEquality]
          exact ⟨nameTyped, by simpa [imageEquality] using nameSafe⟩
        obtain ⟨nameTyped, nameSafe⟩ := nameTypedSafe
        have cancellation := rho_costStatic_quoteDrop_action_canonicalize_eq
          (inner := currentInner) thinning assignment nameTyped rfl nameSafe
            nameSupported nameObject currentAvailable.length
        have lifted := ReflectiveEquationSemantics.canonicalize_fill_congr
          targetDeclaration
          (.apply targetDeclaration.quoteConstructor [] .hole [])
          (by simpa [canonicalEquality] using argumentEquality)
        have lifted' :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (.apply targetDeclaration.quoteConstructor
                  [rhoCostStaticActionAt thinning assignment currentInner []
                    argument]) =
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (.apply targetDeclaration.quoteConstructor
                  [rhoCostStaticActionAt thinning assignment currentInner []
                    (.apply rhoReflectivePresentation.dropConstructor
                      [name])]) := by
          simpa [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill]
            using lifted
        have cancellationAction :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (rhoCostStaticActionAt thinning assignment currentInner
                  currentAvailable
                  (.apply rhoReflectivePresentation.quoteConstructor
                    [.apply rhoReflectivePresentation.dropConstructor
                      [name]])) =
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (rhoCostStaticActionAt thinning assignment currentInner
                  currentAvailable name) := by
          simpa [rhoCostStaticActionAt, rhoReflectivePresentation,
            targetDeclaration] using cancellation
        have cancellation' :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (.apply targetDeclaration.quoteConstructor
                  [rhoCostStaticActionAt thinning assignment currentInner []
                    (.apply rhoReflectivePresentation.dropConstructor
                      [name])]) =
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (rhoCostStaticActionAt thinning assignment currentInner
                  currentAvailable name) := by
          rw [quoteAction] at cancellationAction
          exact cancellationAction
        have canonicalQuote :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation
                (.apply rhoReflectivePresentation.quoteConstructor
                  [argument]) = name := by
          change
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
                rhoReflectivePresentation
                rhoReflectivePresentation.quoteConstructor
                [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  rhoReflectivePresentation argument] = name
          rw [canonicalEquality]
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]
        rw [selectedByQuote, quoteAction, canonicalQuote]
        exact lifted'.trans cancellation'
      · have canonicalQuote :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation
                (.apply rhoReflectivePresentation.quoteConstructor
                  [argument]) =
              .apply rhoReflectivePresentation.quoteConstructor
                [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  rhoReflectivePresentation argument] := by
          change
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
                rhoReflectivePresentation
                rhoReflectivePresentation.quoteConstructor
                [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  rhoReflectivePresentation argument] =
              .apply rhoReflectivePresentation.quoteConstructor
                [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  rhoReflectivePresentation argument]
          exact rho_finishNormalizeReflectiveApply_quote_eq_of_not_drop
            dropShape
        have lifted := ReflectiveEquationSemantics.canonicalize_fill_congr
          targetDeclaration
          (.apply targetDeclaration.quoteConstructor [] .hole [])
          argumentEquality
        rw [selectedByQuote, quoteAction, canonicalQuote, quoteAction]
        simpa [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill]
          using lifted)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        currentAvailable currentImage ordinary argumentsSafe argumentsIH
        currentInner boundEquality imageEquality resultSupported resultObject
      have argumentsSupported : ConstructorListWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) arguments :=
        resultSupported.2
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using resultObject
      have listEquality := argumentsIH currentInner boundEquality imageEquality
        argumentsSupported argumentsObject
      have selected :
          rule.label ≠ rhoReflectivePresentation.quoteConstructor := by
        intro equality
        have sourceQuote : ReflectiveContextSupport.isQuoteConstructor rhoReflectionProfile
            rhoReflectivePresentation.quoteConstructor = true := by
          simp only [ReflectiveContextSupport.isQuoteConstructor,
            List.any_eq_true]
          exact ⟨rhoReflectivePresentation.toReflectivePresentationDecl,
            sourceMembership, by simp⟩
        rw [equality] at ordinary
        exact Bool.noConfusion (ordinary.symm.trans sourceQuote)
      have selectedFalse :
          (rule.label == rhoReflectivePresentation.quoteConstructor) = false :=
        by simp [selected]
      have targetOrdinaryStatus :
          ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
              ((color.symbols rhoCIGSLT).constructor rule.label) = false := by
        rw [reflectiveIsQuoteConstructor_mapCostStatic]
        exact ordinary
      have targetOrdinaryStatusTag :
          ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
              (color.constructorTag ++ rule.label) = false := by
        rw [← CostStaticColor.symbols_constructor]
        exact targetOrdinaryStatus
      have applicationAction (patterns : List Pattern) :
          rhoCostStaticActionAt thinning assignment currentInner
              currentAvailable (.apply rule.label patterns) =
            .apply ((color.symbols rhoCIGSLT).constructor rule.label)
              (patterns.map (rhoCostStaticActionAt thinning assignment
                currentInner currentAvailable)) := by
        simp [rhoCostStaticActionAt,
          ReflectiveContextSupport.substituteAt,
          CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
          targetOrdinaryStatusTag, List.map_map, Function.comp_def]
      have canonicalApplication :
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              rhoReflectivePresentation (.apply rule.label arguments) =
            .apply rule.label
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                rhoReflectivePresentation arguments) := by
        simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
          selectedFalse]
      rw [canonicalApplication, applicationAction, applicationAction]
      simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
      rw [listEquality])
    (by
      intro bound binder body domain codomain bodyTyped currentAvailable
        currentImage bodySafe bodyIH currentInner boundEquality imageEquality
        resultSupported resultObject
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using resultObject
      have bodyBound : domain :: bound =
          (domain :: currentInner) ++ sourceBound := by
        simp [boundEquality]
      have bodyEquality := bodyIH (domain :: currentInner) bodyBound
        imageEquality resultSupported bodyObject
      simpa [rhoCostStaticActionAt,
        ReflectiveContextSupport.substituteAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        CostStaticBinderThinning.thickenAmbientBVars, mapPattern]
        using congrArg (Pattern.lambda binder) bodyEquality)
    (by
      intro bound arity binders body domain codomain bodyTyped currentAvailable
        currentImage bodySafe bodyIH currentInner boundEquality imageEquality
        resultSupported resultObject
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using resultObject
      have bodyBound : List.replicate arity domain ++ bound =
          (List.replicate arity domain ++ currentInner) ++ sourceBound := by
        simp [boundEquality, List.append_assoc]
      have bodyEquality := bodyIH
        (List.replicate arity domain ++ currentInner) bodyBound imageEquality
          resultSupported bodyObject
      simpa [rhoCostStaticActionAt,
        ReflectiveContextSupport.substituteAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
        List.length_append, List.length_replicate,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using congrArg (Pattern.multiLambda arity binders) bodyEquality)
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        currentAvailable currentImage bodySafe replacementSafe bodyIH replacementIH
        currentInner boundEquality imageEquality resultSupported resultObject
      simp [isObjectPattern] at resultObject)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        currentAvailable currentImage elementsSafe elementsIH currentInner
        boundEquality imageEquality resultSupported resultObject
      have objectParts : rest = none ∧ isObjectPatternList elements = true := by
        simpa [isObjectPattern] using resultObject
      rcases objectParts with ⟨rfl, elementsObject⟩
      have listEquality := elementsIH currentInner boundEquality imageEquality
        resultSupported elementsObject
      let action := rhoCostStaticActionAt thinning assignment currentInner
        currentAvailable
      have actionCollection (selectedCollectionType : CollType)
          (patterns : List Pattern) :
          action (.collection selectedCollectionType patterns none) =
            .collection selectedCollectionType (patterns.map action) none := by
        simp [action, rhoCostStaticActionAt,
          ReflectiveContextSupport.substituteAt,
          CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
          List.map_map, Function.comp_def]
      by_cases parallelShape :
          collectionType = rhoReflectivePresentation.parallelCollection
      · subst collectionType
        have mapParallel : ∀ patterns,
            action
                (.collection rhoReflectivePresentation.parallelCollection
                  patterns none) =
              .collection targetDeclaration.parallelCollection
                (patterns.map action) none := by
          intro patterns
          simp [action, rhoCostStaticActionAt, targetDeclaration,
            ReflectiveContextSupport.substituteAt,
            CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
            mapReflectivePresentation]
        have mapUnit :
            action (.apply rhoReflectivePresentation.parallelUnitConstructor []) =
              .apply targetDeclaration.parallelUnitConstructor [] := by
          simp [action, rhoCostStaticActionAt, targetDeclaration,
            ReflectiveContextSupport.substituteAt,
            CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
            mapReflectivePresentation]
        have childrenEquality :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (.collection targetDeclaration.parallelCollection
                  (elements.map action) none) =
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (.collection targetDeclaration.parallelCollection
                  ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                    rhoReflectivePresentation elements).map action) none) := by
          simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
            beq_self_eq_true, if_true]
          rw [listEquality]
        have normalized :=
          ReflectiveParallelSubstitution.normalizationMapCanonicalizeEqBetween
            rhoReflectivePresentation targetDeclaration action mapParallel
              mapUnit
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                rhoReflectivePresentation elements)
        have canonicalCollection :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation
                (.collection rhoReflectivePresentation.parallelCollection
                  elements none) =
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                rhoReflectivePresentation
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
                  rhoReflectivePresentation
                  (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                    rhoReflectivePresentation elements)) := by
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
        change
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              targetDeclaration
              (action (.collection
                rhoReflectivePresentation.parallelCollection elements none)) =
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              targetDeclaration
              (action
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  rhoReflectivePresentation
                  (.collection rhoReflectivePresentation.parallelCollection
                    elements none)))
        rw [canonicalCollection, mapParallel]
        exact childrenEquality.trans normalized
      · have selectedFalse :
            (collectionType == rhoReflectivePresentation.parallelCollection) =
              false := by simp [parallelShape]
        have canonicalCollection :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation
                (.collection collectionType elements none) =
              .collection collectionType
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                  rhoReflectivePresentation elements) none := by
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
            selectedFalse]
        change
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              targetDeclaration
              (action (.collection collectionType elements none)) =
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              targetDeclaration
              (action
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  rhoReflectivePresentation
                  (.collection collectionType elements none)))
        rw [canonicalCollection, actionCollection, actionCollection]
        simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
        rw [listEquality])
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped currentAvailable currentImage
        elementsSafe elementsIH currentInner boundEquality imageEquality
        resultSupported resultObject
      have objectParts : rest = none ∧ isObjectPatternList elements = true := by
        simpa [isObjectPattern] using resultObject
      rcases objectParts with ⟨rfl, elementsObject⟩
      have listEquality := elementsIH currentInner boundEquality imageEquality
        resultSupported elementsObject
      let action := rhoCostStaticActionAt thinning assignment currentInner
        currentAvailable
      have actionCollection (selectedCollectionType : CollType)
          (patterns : List Pattern) :
          action (.collection selectedCollectionType patterns none) =
            .collection selectedCollectionType (patterns.map action) none := by
        simp [action, rhoCostStaticActionAt,
          ReflectiveContextSupport.substituteAt,
          CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
          List.map_map, Function.comp_def]
      by_cases parallelShape :
          collectionType = rhoReflectivePresentation.parallelCollection
      · subst collectionType
        have mapParallel : ∀ patterns,
            action
                (.collection rhoReflectivePresentation.parallelCollection
                  patterns none) =
              .collection targetDeclaration.parallelCollection
                (patterns.map action) none := by
          intro patterns
          simp [action, rhoCostStaticActionAt, targetDeclaration,
            ReflectiveContextSupport.substituteAt,
            CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
            mapReflectivePresentation]
        have mapUnit :
            action (.apply rhoReflectivePresentation.parallelUnitConstructor []) =
              .apply targetDeclaration.parallelUnitConstructor [] := by
          simp [action, rhoCostStaticActionAt, targetDeclaration,
            ReflectiveContextSupport.substituteAt,
            CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
            mapReflectivePresentation]
        have childrenEquality :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (.collection targetDeclaration.parallelCollection
                  (elements.map action) none) =
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (.collection targetDeclaration.parallelCollection
                  ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                    rhoReflectivePresentation elements).map action) none) := by
          simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
            beq_self_eq_true, if_true]
          rw [listEquality]
        have normalized :=
          ReflectiveParallelSubstitution.normalizationMapCanonicalizeEqBetween
            rhoReflectivePresentation targetDeclaration action mapParallel
              mapUnit
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                rhoReflectivePresentation elements)
        have canonicalCollection :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation
                (.collection rhoReflectivePresentation.parallelCollection
                  elements none) =
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                rhoReflectivePresentation
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
                  rhoReflectivePresentation
                  (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                    rhoReflectivePresentation elements)) := by
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
        change
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              targetDeclaration
              (action (.collection
                rhoReflectivePresentation.parallelCollection elements none)) =
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              targetDeclaration
              (action
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  rhoReflectivePresentation
                  (.collection rhoReflectivePresentation.parallelCollection
                    elements none)))
        rw [canonicalCollection, mapParallel]
        exact childrenEquality.trans normalized
      · have selectedFalse :
            (collectionType == rhoReflectivePresentation.parallelCollection) =
              false := by simp [parallelShape]
        have canonicalCollection :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation
                (.collection collectionType elements none) =
              .collection collectionType
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                  rhoReflectivePresentation elements) none := by
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
            selectedFalse]
        change
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              targetDeclaration
              (action (.collection collectionType elements none)) =
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              targetDeclaration
              (action
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  rhoReflectivePresentation
                  (.collection collectionType elements none)))
        rw [canonicalCollection, actionCollection, actionCollection]
        simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
        rw [listEquality])
    (by
      intro bound currentAvailable currentImage currentInner boundEquality
        imageEquality argumentsSupported argumentsObject
      rfl)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable currentImage argumentSafe argumentsSafe argumentIH
        argumentsIH currentInner boundEquality imageEquality argumentsSupported
        argumentsObject
      have objectParts : isObjectPattern argument = true ∧
          isObjectPatternList arguments = true := by
        simpa [isObjectPatternList] using argumentsObject
      simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
        List.map_cons]
      rw [argumentIH currentInner boundEquality imageEquality
          argumentsSupported.1 objectParts.1,
        argumentsIH currentInner boundEquality imageEquality
          argumentsSupported.2 objectParts.2])
    (by
      intro bound elementType currentAvailable currentImage currentInner
        boundEquality imageEquality elementsSupported elementsObject
      rfl)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        currentAvailable currentImage elementSafe elementsSafe elementIH
        elementsIH currentInner boundEquality imageEquality elementsSupported
        elementsObject
      have objectParts : isObjectPattern element = true ∧
          isObjectPatternList elements = true := by
        simpa [isObjectPatternList] using elementsObject
      simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
        List.map_cons]
      rw [elementIH currentInner boundEquality imageEquality
          elementsSupported.1 objectParts.1,
        elementsIH currentInner boundEquality imageEquality
          elementsSupported.2 objectParts.2])
    safe inner rfl rfl supported object

/-- Equal authored rho canonical representatives remain exactly equal after
the same typed same-colour Cost action.

This is the two-endpoint form of
`rhoCostStaticActionAt_canonicalize_eq`.  Its hypotheses expose the whole
shared action fibre: the binder thinning, supported assignment, free-context
image, and reflective-support image are common to both endpoints.  No claim
is made for independently chosen actions or for arbitrary generated terms. -/
theorem rhoCostStaticActionAt_canonicalize_eq_of_canonicalize_eq
    {color : CostStaticColor}
    {free assignmentFree targetFree : FreeTypeContext}
    {support assignmentSupport : ContextSupport.Support}
    {sourceBound targetBound inner available : List TypeExpr}
    {left right : Pattern} {leftType rightType : TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    (assignment : SupportedOpenAssignment rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      assignmentFree targetFree assignmentSupport)
    (freeContext : free.map (color.symbols rhoCIGSLT) = assignmentFree)
    (reflectiveSupport : support = assignmentSupport)
    (leftTyped : HasType rhoCalc free (inner ++ sourceBound) left leftType)
    (rightTyped : HasType rhoCalc free (inner ++ sourceBound) right rightType)
    (leftSafe : leftTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available
      (mapTypeExpr (color.symbols rhoCIGSLT)))
    (rightSafe : rightTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available
      (mapTypeExpr (color.symbols rhoCIGSLT)))
    (leftSupported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) left)
    (rightSupported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) right)
    (leftObject : isObjectPattern left = true)
    (rightObject : isObjectPattern right = true)
    (canonical :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          rhoReflectivePresentation left =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          rhoReflectivePresentation right) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (rhoCostStaticActionAt thinning assignment inner available left) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (rhoCostStaticActionAt thinning assignment inner available right) := by
  have leftAbsorption := rhoCostStaticActionAt_canonicalize_eq
    thinning assignment freeContext reflectiveSupport leftTyped leftSafe
      leftSupported leftObject
  have rightAbsorption := rhoCostStaticActionAt_canonicalize_eq
    thinning assignment freeContext reflectiveSupport rightTyped rightSafe
      rightSupported rightObject
  rw [canonical] at leftAbsorption
  exact leftAbsorption.trans rightAbsorption.symm

/-- Canonicalizing one constructor-certified rho skeleton before its
same-colour Cost action is observationally neutral in the generated authored
equation relation.  The induction is source typed: this retains the exact
binder slice that the mixed-colour raw target language cannot reconstruct. -/
theorem rhoCostStaticActionAt_canonicalize_equationEquiv
    {color : CostStaticColor}
    {free assignmentFree targetFree : FreeTypeContext}
    {support assignmentSupport : ContextSupport.Support}
    {sourceBound targetBound inner available : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    (assignment : SupportedOpenAssignment rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      assignmentFree targetFree assignmentSupport)
    (freeContext : free.map (color.symbols rhoCIGSLT) = assignmentFree)
    (reflectiveSupport : support = assignmentSupport)
    (typed : HasType rhoCalc free (inner ++ sourceBound) pattern type)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available
      (mapTypeExpr (color.symbols rhoCIGSLT)))
    (supported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) pattern)
    (object : isObjectPattern pattern = true) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage
      (rhoCostStaticActionAt thinning assignment inner available pattern)
      (rhoCostStaticActionAt thinning assignment inner available
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          rhoReflectivePresentation pattern)) := by
  subst assignmentFree
  subst assignmentSupport
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have sourceMembership :
      rhoReflectivePresentation.toReflectivePresentationDecl ∈
        rhoReflectionProfile.presentations := by
    simp [rhoReflectionProfile]
  have targetMembership : targetDeclaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [targetDeclaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl sourceMembership
  have targetQuoteStatus :
      ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
          ((color.symbols rhoCIGSLT).constructor
            rhoReflectivePresentation.quoteConstructor) = true := by
    rw [reflectiveIsQuoteConstructor_mapCostStatic]
    rw [rhoCIGSLT_reflectionProfile_eq]
    simp [rhoReflectionProfile, ReflectiveContextSupport.isQuoteConstructor,
      rhoReflectivePresentation]
  have targetDropStatus :
      ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
          ((color.symbols rhoCIGSLT).constructor
            rhoReflectivePresentation.dropConstructor) = false := by
    rw [reflectiveIsQuoteConstructor_mapCostStatic]
    rw [rhoCIGSLT_reflectionProfile_eq]
    simp [rhoReflectionProfile, ReflectiveContextSupport.isQuoteConstructor,
      rhoReflectivePresentation]
  have targetDeclarationQuote : targetDeclaration.quoteConstructor =
      (color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor := by
    simp [targetDeclaration, mapReflectivePresentation]
  have targetQuoteStatusTag :
      ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
          (color.constructorTag ++
            rhoReflectivePresentation.quoteConstructor) = true := by
    rw [← CostStaticColor.symbols_constructor]
    exact targetQuoteStatus
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType rhoCalc free bound pattern type)
      (currentAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        currentAvailable currentImage) =>
      ∀ (currentInner : List TypeExpr),
        bound = currentInner ++ sourceBound →
        currentImage = mapTypeExpr (color.symbols rhoCIGSLT) →
        ConstructorsWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) pattern →
        isObjectPattern pattern = true →
        ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage
          (rhoCostStaticActionAt thinning assignment currentInner
            currentAvailable pattern)
          (rhoCostStaticActionAt thinning assignment currentInner
            currentAvailable
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              rhoReflectivePresentation pattern)))
    (motive_2 := fun {bound arguments parameters}
      (typed : ArgumentsHaveTypes rhoCalc free bound arguments parameters)
      (currentAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        currentAvailable currentImage) =>
      ∀ (currentInner : List TypeExpr),
        bound = currentInner ++ sourceBound →
        currentImage = mapTypeExpr (color.symbols rhoCIGSLT) →
        ConstructorListWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) arguments →
        isObjectPatternList arguments = true →
        List.Forall₂
          (ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage)
          (arguments.map
            (rhoCostStaticActionAt thinning assignment currentInner
              currentAvailable))
          ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              rhoReflectivePresentation arguments).map
            (rhoCostStaticActionAt thinning assignment currentInner
              currentAvailable)))
    (motive_3 := fun {bound elements elementType}
      (typed : ElementsHaveType rhoCalc free bound elements elementType)
      (currentAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        currentAvailable currentImage) =>
      ∀ (currentInner : List TypeExpr),
        bound = currentInner ++ sourceBound →
        currentImage = mapTypeExpr (color.symbols rhoCIGSLT) →
        ConstructorListWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) elements →
        isObjectPatternList elements = true →
        List.Forall₂
          (ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage)
          (elements.map
            (rhoCostStaticActionAt thinning assignment currentInner
              currentAvailable))
          ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              rhoReflectivePresentation elements).map
            (rhoCostStaticActionAt thinning assignment currentInner
              currentAvailable)))
    (by
      intro bound index resultType lookup currentAvailable currentImage
        currentInner boundEquality imageEquality resultSupported resultObject
      exact Relation.EqvGen.refl _)
    (by
      intro bound freeName resultType lookup currentAvailable currentImage shape
        currentInner boundEquality imageEquality resultSupported resultObject
      exact Relation.EqvGen.refl _)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        currentAvailable currentImage quoted argumentsSafe argumentsIH
        currentInner boundEquality imageEquality resultSupported resultObject
      have argumentsSupported : ConstructorListWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) arguments :=
        resultSupported.2
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using resultObject
      have pointwise := argumentsIH currentInner boundEquality imageEquality
        argumentsSupported argumentsObject
      have lifted := ReflectiveEquationSemantics.equationEquiv_apply_of_forall₂
        ((color.symbols rhoCIGSLT).constructor rule.label) pointwise
      have selectedByQuote :
          rule.label = rhoReflectivePresentation.quoteConstructor := by
        unfold ReflectiveContextSupport.isQuoteConstructor at quoted
        rw [List.any_eq_true] at quoted
        obtain ⟨declaration, declarationMembership, quoteLabel⟩ := quoted
        have declarationEquality : declaration =
            rhoReflectivePresentation.toReflectivePresentationDecl := by
          simpa [rhoReflectionProfile] using declarationMembership
        subst declaration
        have quoteLabel' :
            rhoReflectivePresentation.quoteConstructor = rule.label := by
          simpa using quoteLabel
        exact quoteLabel'.symm
      by_cases selected :
          rule.label = rhoReflectivePresentation.quoteConstructor
      · obtain ⟨argument, argumentTyped, rfl, argumentSafe⟩ :=
          argumentsTyped.selectedQuoteArgument
            LanguageDefAdequacy.rhoCalc_validate
              rhoCalcValidatedReflective.admittedReflection.2 sourceMembership
              membership selected argumentsSafe
        have argumentSupported : ConstructorsWithin
            (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) argument :=
          argumentsSupported.1
        have argumentObject : isObjectPattern argument = true := by
          simpa [isObjectPatternList] using argumentsObject
        cases pointwise with
        | @cons _ _ _ _ argumentEquivalent tailPointwise =>
            cases tailPointwise
            have lifted' :
                ReflectiveEquationSemantics.ReflectiveEquationEquiv
                  rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
                  rhoCIGSLT.costWholeLanguage
                (.apply targetDeclaration.quoteConstructor
                  [rhoCostStaticActionAt thinning assignment currentInner []
                    argument])
                (.apply targetDeclaration.quoteConstructor
                  [rhoCostStaticActionAt thinning assignment currentInner []
                    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                      rhoReflectivePresentation argument)]) := by
              simpa [targetDeclaration, selected,
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
                costStaticReflectivePresentationDecl,
                costBaseReflectivePresentationDecl,
                costWrappedReflectivePresentationDecl,
                mapReflectivePresentation] using lifted
            have quoteAction (payload : Pattern) :
                rhoCostStaticActionAt thinning assignment currentInner
                    currentAvailable
                    (.apply rhoReflectivePresentation.quoteConstructor
                      [payload]) =
                  .apply targetDeclaration.quoteConstructor
                      [rhoCostStaticActionAt thinning assignment currentInner []
                      payload] := by
              rw [targetDeclarationQuote]
              simp [rhoCostStaticActionAt,
                ReflectiveContextSupport.substituteAt,
                CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
                targetQuoteStatusTag]
            by_cases dropShape : ∃ name,
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                    rhoReflectivePresentation argument =
                  .apply rhoReflectivePresentation.dropConstructor [name]
            · obtain ⟨name, canonicalEquality⟩ := dropShape
              obtain ⟨nameTyped, nameSafe, nameObject⟩ :=
                EquationSubstitution.rho_reflectiveDropCanonicalSupportStable
                  rhoReflectivePresentation.toReflectivePresentationDecl
                    sourceMembership argumentTyped argumentSafe argumentObject
                      canonicalEquality
              have canonicalSupported : ConstructorsWithin
                  (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels)
                  (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                    rhoReflectivePresentation argument) :=
                (constructorsWithin_canonicalize_iff rhoReflectivePresentation
                  rho_costReflectiveConstructorsAllowed argument).2
                    argumentSupported
              rw [canonicalEquality] at canonicalSupported
              have nameSupported : ConstructorsWithin
                  (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) name :=
                canonicalSupported.2.1
              have nameTypedSafe :
                  ∃ nameTyped' : HasType rhoCalc free
                      (currentInner ++ sourceBound) name
                      (.base rhoReflectivePresentation.nameSort),
                    nameTyped'.ReflectiveSupportSafeAt rhoReflectionProfile
                      support []
                      (mapTypeExpr (color.symbols rhoCIGSLT)) := by
                rw [← boundEquality]
                exact ⟨nameTyped, by simpa [imageEquality] using nameSafe⟩
              obtain ⟨nameTyped, nameSafe⟩ := nameTypedSafe
              have cancellation := rho_costStatic_quoteDrop_action
                (inner := currentInner) thinning assignment nameTyped rfl
                  nameSafe nameSupported
                    nameObject currentAvailable.length
              rw [canonicalEquality] at lifted'
              have cancellationAction :
                  ReflectiveEquationSemantics.ReflectiveEquationEquiv
                    rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
                    rhoCIGSLT.costWholeLanguage
                    (rhoCostStaticActionAt thinning assignment currentInner
                      currentAvailable
                      (.apply rhoReflectivePresentation.quoteConstructor
                        [.apply rhoReflectivePresentation.dropConstructor
                          [name]]))
                    (rhoCostStaticActionAt thinning assignment currentInner
                      currentAvailable name) := by
                simpa [rhoCostStaticActionAt, rhoReflectivePresentation]
                  using cancellation
              rw [quoteAction] at cancellationAction
              have cancellation' :
                  ReflectiveEquationSemantics.ReflectiveEquationEquiv
                    rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
                    rhoCIGSLT.costWholeLanguage
                    (.apply targetDeclaration.quoteConstructor
                      [rhoCostStaticActionAt thinning assignment currentInner []
                        (.apply rhoReflectivePresentation.dropConstructor
                          [name])])
                    (rhoCostStaticActionAt thinning assignment currentInner
                      currentAvailable name) := by
                exact cancellationAction
              have canonicalQuote :
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                      rhoReflectivePresentation
                      (.apply rhoReflectivePresentation.quoteConstructor
                        [argument]) = name := by
                change
                  Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
                      rhoReflectivePresentation
                      rhoReflectivePresentation.quoteConstructor
                      [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                        rhoReflectivePresentation argument] = name
                rw [canonicalEquality]
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]
              rw [selected]
              rw [quoteAction, canonicalQuote]
              exact rhoCostEquationEquiv_trans lifted' cancellation'
            · have quotedCanonical :=
                rho_finishNormalizeReflectiveApply_quote_eq_of_not_drop
                  dropShape
              have canonicalQuote :
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                      rhoReflectivePresentation
                      (.apply rhoReflectivePresentation.quoteConstructor
                        [argument]) =
                    .apply rhoReflectivePresentation.quoteConstructor
                      [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                        rhoReflectivePresentation argument] := by
                change
                  Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
                      rhoReflectivePresentation
                      rhoReflectivePresentation.quoteConstructor
                      [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                        rhoReflectivePresentation argument] =
                    .apply rhoReflectivePresentation.quoteConstructor
                      [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                        rhoReflectivePresentation argument]
                exact quotedCanonical
              rw [selected]
              rw [quoteAction, canonicalQuote, quoteAction]
              exact lifted'
      · exact False.elim (selected selectedByQuote))
    (by
      intro bound rule arguments membership notBare argumentsTyped
        currentAvailable currentImage ordinary argumentsSafe argumentsIH
        currentInner boundEquality imageEquality resultSupported resultObject
      have argumentsSupported : ConstructorListWithin
          (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) arguments :=
        resultSupported.2
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using resultObject
      have pointwise := argumentsIH currentInner boundEquality imageEquality
        argumentsSupported argumentsObject
      have lifted := ReflectiveEquationSemantics.equationEquiv_apply_of_forall₂
        ((color.symbols rhoCIGSLT).constructor rule.label) pointwise
      have selected :
          rule.label ≠ rhoReflectivePresentation.quoteConstructor := by
        intro equality
        have sourceQuote : ReflectiveContextSupport.isQuoteConstructor rhoReflectionProfile
            rhoReflectivePresentation.quoteConstructor = true := by
          simp only [ReflectiveContextSupport.isQuoteConstructor,
            List.any_eq_true]
          exact ⟨rhoReflectivePresentation.toReflectivePresentationDecl,
            sourceMembership, by simp⟩
        rw [equality] at ordinary
        exact Bool.noConfusion (ordinary.symm.trans sourceQuote)
      have selectedFalse :
          (rule.label == rhoReflectivePresentation.quoteConstructor) = false :=
        by simp [selected]
      have targetOrdinaryStatus :
          ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
              ((color.symbols rhoCIGSLT).constructor rule.label) = false := by
        rw [reflectiveIsQuoteConstructor_mapCostStatic]
        exact ordinary
      have targetOrdinaryStatusTag :
          ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
              (color.constructorTag ++ rule.label) = false := by
        rw [← CostStaticColor.symbols_constructor]
        exact targetOrdinaryStatus
      have applicationAction (patterns : List Pattern) :
          rhoCostStaticActionAt thinning assignment currentInner
              currentAvailable (.apply rule.label patterns) =
            .apply ((color.symbols rhoCIGSLT).constructor rule.label)
              (patterns.map (rhoCostStaticActionAt thinning assignment
                currentInner currentAvailable)) := by
        simp [rhoCostStaticActionAt,
          ReflectiveContextSupport.substituteAt,
          CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
          targetOrdinaryStatusTag, List.map_map, Function.comp_def]
      have canonicalApplication :
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              rhoReflectivePresentation (.apply rule.label arguments) =
            .apply rule.label
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                rhoReflectivePresentation arguments) := by
        simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
          selectedFalse]
      rw [canonicalApplication, applicationAction, applicationAction]
      exact lifted)
    (by
      intro bound binder body domain codomain bodyTyped currentAvailable
        currentImage bodySafe bodyIH currentInner boundEquality imageEquality
        resultSupported resultObject
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using resultObject
      have bodyBound : domain :: bound =
          (domain :: currentInner) ++ sourceBound := by
        simp [boundEquality]
      have bodyEquivalent := bodyIH (domain :: currentInner) bodyBound
        imageEquality resultSupported bodyObject
      have lifted := ReflectiveEquationSemantics.equationEquiv_fill
        (.lambda binder .hole) bodyEquivalent
      simpa [rhoCostStaticActionAt,
        ReflectiveContextSupport.substituteAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
        Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill] using lifted)
    (by
      intro bound arity binders body domain codomain bodyTyped currentAvailable
        currentImage bodySafe bodyIH currentInner boundEquality imageEquality
        resultSupported resultObject
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using resultObject
      have bodyBound : List.replicate arity domain ++ bound =
          (List.replicate arity domain ++ currentInner) ++ sourceBound := by
        simp [boundEquality, List.append_assoc]
      have bodyEquivalent := bodyIH
        (List.replicate arity domain ++ currentInner) bodyBound imageEquality
          resultSupported bodyObject
      have lifted := ReflectiveEquationSemantics.equationEquiv_fill
        (.multiLambda arity binders .hole) bodyEquivalent
      simpa [rhoCostStaticActionAt,
        ReflectiveContextSupport.substituteAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
        Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
        List.length_append, List.length_replicate,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using lifted)
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        currentAvailable currentImage bodySafe replacementSafe bodyIH replacementIH
        currentInner boundEquality imageEquality resultSupported resultObject
      simp [isObjectPattern] at resultObject)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        currentAvailable currentImage elementsSafe elementsIH currentInner
        boundEquality imageEquality resultSupported resultObject
      have objectParts : rest = none ∧ isObjectPatternList elements = true := by
        simpa [isObjectPattern] using resultObject
      rcases objectParts with ⟨rfl, elementsObject⟩
      have pointwise := elementsIH currentInner boundEquality imageEquality
        resultSupported elementsObject
      have lifted := ReflectiveEquationSemantics.equationEquiv_collection_of_forall₂
        collectionType none pointwise
      let action := rhoCostStaticActionAt thinning assignment currentInner
        currentAvailable
      have actionCollection (selectedCollectionType : CollType)
          (patterns : List Pattern) :
          action (.collection selectedCollectionType patterns none) =
            .collection selectedCollectionType (patterns.map action) none := by
        simp [action, rhoCostStaticActionAt,
          ReflectiveContextSupport.substituteAt,
          CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
          List.map_map, Function.comp_def]
      by_cases parallelShape :
          collectionType = rhoReflectivePresentation.parallelCollection
      · subst collectionType
        have mapParallel : ∀ patterns,
            action
                (.collection rhoReflectivePresentation.parallelCollection
                  patterns none) =
              .collection targetDeclaration.parallelCollection
                (patterns.map action) none := by
          intro patterns
          simp [action, rhoCostStaticActionAt, targetDeclaration,
            ReflectiveContextSupport.substituteAt,
            CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
            mapReflectivePresentation]
        have mapUnit :
            action (.apply rhoReflectivePresentation.parallelUnitConstructor []) =
              .apply targetDeclaration.parallelUnitConstructor [] := by
          simp [action, rhoCostStaticActionAt, targetDeclaration,
            ReflectiveContextSupport.substituteAt,
            CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
            mapReflectivePresentation]
        have normalized :=
          ReflectiveParallelSubstitution.normalizationMapEquivalentBetween
            (language := rhoCIGSLT.costWholeLanguage)
            rhoReflectivePresentation targetMembership action mapParallel mapUnit
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                rhoReflectivePresentation elements)
        have lifted' : ReflectiveEquationSemantics.ReflectiveEquationEquiv
            rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
            rhoCIGSLT.costWholeLanguage
            (action (.collection rhoReflectivePresentation.parallelCollection
              elements none))
            (.collection targetDeclaration.parallelCollection
              ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                rhoReflectivePresentation elements).map action) none) := by
          rw [mapParallel]
          simpa [targetDeclaration,
            costStaticReflectivePresentationDecl,
            costBaseReflectivePresentationDecl,
            costWrappedReflectivePresentationDecl, mapReflectivePresentation]
            using lifted
        have canonicalCollection :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation
                (.collection rhoReflectivePresentation.parallelCollection
                  elements none) =
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                rhoReflectivePresentation
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
                  rhoReflectivePresentation
                  (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                    rhoReflectivePresentation elements)) := by
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
        rw [canonicalCollection]
        exact rhoCostEquationEquiv_trans lifted' normalized
      · have selectedFalse :
            (collectionType == rhoReflectivePresentation.parallelCollection) =
              false := by simp [parallelShape]
        have canonicalCollection :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation
                (.collection collectionType elements none) =
              .collection collectionType
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                  rhoReflectivePresentation elements) none := by
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
            selectedFalse]
        rw [canonicalCollection]
        change ReflectiveEquationSemantics.ReflectiveEquationEquiv
          rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
          rhoCIGSLT.costWholeLanguage
          (action (.collection collectionType elements none))
          (action (.collection collectionType
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              rhoReflectivePresentation elements) none))
        rw [actionCollection, actionCollection]
        exact lifted)
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped currentAvailable currentImage
        elementsSafe elementsIH currentInner boundEquality imageEquality
        resultSupported resultObject
      have objectParts : rest = none ∧ isObjectPatternList elements = true := by
        simpa [isObjectPattern] using resultObject
      rcases objectParts with ⟨rfl, elementsObject⟩
      have pointwise := elementsIH currentInner boundEquality imageEquality
        resultSupported elementsObject
      have lifted := ReflectiveEquationSemantics.equationEquiv_collection_of_forall₂
        collectionType none pointwise
      let action := rhoCostStaticActionAt thinning assignment currentInner
        currentAvailable
      have actionCollection (selectedCollectionType : CollType)
          (patterns : List Pattern) :
          action (.collection selectedCollectionType patterns none) =
            .collection selectedCollectionType (patterns.map action) none := by
        simp [action, rhoCostStaticActionAt,
          ReflectiveContextSupport.substituteAt,
          CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
          List.map_map, Function.comp_def]
      by_cases parallelShape :
          collectionType = rhoReflectivePresentation.parallelCollection
      · subst collectionType
        have mapParallel : ∀ patterns,
            action
                (.collection rhoReflectivePresentation.parallelCollection
                  patterns none) =
              .collection targetDeclaration.parallelCollection
                (patterns.map action) none := by
          intro patterns
          simp [action, rhoCostStaticActionAt, targetDeclaration,
            ReflectiveContextSupport.substituteAt,
            CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
            mapReflectivePresentation]
        have mapUnit :
            action (.apply rhoReflectivePresentation.parallelUnitConstructor []) =
              .apply targetDeclaration.parallelUnitConstructor [] := by
          simp [action, rhoCostStaticActionAt, targetDeclaration,
            ReflectiveContextSupport.substituteAt,
            CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
            mapReflectivePresentation]
        have normalized :=
          ReflectiveParallelSubstitution.normalizationMapEquivalentBetween
            (language := rhoCIGSLT.costWholeLanguage)
            rhoReflectivePresentation targetMembership action mapParallel mapUnit
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                rhoReflectivePresentation elements)
        have lifted' : ReflectiveEquationSemantics.ReflectiveEquationEquiv
            rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
            rhoCIGSLT.costWholeLanguage
            (action (.collection rhoReflectivePresentation.parallelCollection
              elements none))
            (.collection targetDeclaration.parallelCollection
              ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                rhoReflectivePresentation elements).map action) none) := by
          rw [mapParallel]
          simpa [targetDeclaration,
            costStaticReflectivePresentationDecl,
            costBaseReflectivePresentationDecl,
            costWrappedReflectivePresentationDecl, mapReflectivePresentation]
            using lifted
        have canonicalCollection :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation
                (.collection rhoReflectivePresentation.parallelCollection
                  elements none) =
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                rhoReflectivePresentation
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
                  rhoReflectivePresentation
                  (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                    rhoReflectivePresentation elements)) := by
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
        rw [canonicalCollection]
        exact rhoCostEquationEquiv_trans lifted' normalized
      · have selectedFalse :
            (collectionType == rhoReflectivePresentation.parallelCollection) =
              false := by simp [parallelShape]
        have canonicalCollection :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                rhoReflectivePresentation
                (.collection collectionType elements none) =
              .collection collectionType
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                  rhoReflectivePresentation elements) none := by
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
            selectedFalse]
        rw [canonicalCollection]
        change ReflectiveEquationSemantics.ReflectiveEquationEquiv
          rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
          rhoCIGSLT.costWholeLanguage
          (action (.collection collectionType elements none))
          (action (.collection collectionType
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              rhoReflectivePresentation elements) none))
        rw [actionCollection, actionCollection]
        exact lifted)
    (by
      intro bound currentAvailable currentImage currentInner boundEquality
        imageEquality argumentsSupported argumentsObject
      exact .nil)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable currentImage argumentSafe argumentsSafe argumentIH
        argumentsIH currentInner boundEquality imageEquality argumentsSupported
        argumentsObject
      have objectParts : isObjectPattern argument = true ∧
          isObjectPatternList arguments = true := by
        simpa [isObjectPatternList] using argumentsObject
      exact .cons
        (argumentIH currentInner boundEquality imageEquality
          argumentsSupported.1 objectParts.1)
        (argumentsIH currentInner boundEquality imageEquality
          argumentsSupported.2 objectParts.2))
    (by
      intro bound elementType currentAvailable currentImage currentInner
        boundEquality imageEquality elementsSupported elementsObject
      exact .nil)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        currentAvailable currentImage elementSafe elementsSafe elementIH
        elementsIH currentInner boundEquality imageEquality elementsSupported
        elementsObject
      have objectParts : isObjectPattern element = true ∧
          isObjectPatternList elements = true := by
        simpa [isObjectPatternList] using elementsObject
      exact .cons
        (elementIH currentInner boundEquality imageEquality
          elementsSupported.1 objectParts.1)
        (elementsIH currentInner boundEquality imageEquality
          elementsSupported.2 objectParts.2))
    safe inner rfl rfl supported object

/-- Every bounded instance of either generated rho QuoteDrop declaration is
already collapsed by the matching generated reflective declaration.  Thus
the equation and reflective tables of the sole generated `LanguageDef` agree
on their shared authored law without introducing another canonicalizer. -/
theorem rho_costEquationInstanceAt_canonicalize_eq
    {fuel : Nat} {source target : Pattern}
    (witness : EquationSemantics.EquationInstanceAt defaultBasePremises
      rhoCIGSLT.costWholeLanguage fuel source target) :
    ∃ declaration ∈ rhoCIGSLT.costWholeReflectionProfile.presentations,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          source =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          target := by
  cases witness with
  | @forward equation source target initialBindings finalBindings membership
      matched premises targetEquality =>
      have membership' : equation ∈ rhoCIGSLT.costStaticEquations := by
        change equation ∈ rhoCIGSLT.costStaticEquations at membership
        exact membership
      obtain ⟨color, sourceEquation, sourceMembership, equationEquality⟩ :=
        (mem_costStaticEquations_iff_exists_source rhoCIGSLT).1 membership'
      have sourceEquationEquality :
          sourceEquation = rhoCalc.equations[0] := by
        change sourceEquation ∈ [rhoCalc.equations[0]] at sourceMembership
        simpa using sourceMembership
      subst sourceEquation
      subst equation
      have premisesEmpty :
          (costStaticEquationDecl rhoCIGSLT color
            rhoCalc.equations[0]).premises = [] := by
        apply costStaticEquationDecl_premises
        rfl
      rw [premisesEmpty] at premises
      cases premises
      have matchCorrect :
          Pattern.isMatchCorrect
            (costStaticEquationDecl rhoCIGSLT color
              rhoCalc.equations[0]).left = true := by
        cases color <;> decide
      have sourceEquality := matchPattern_correct matched matchCorrect
      refine ⟨costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl, ?_, ?_⟩
      · change costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl ∈
            rhoCIGSLT.costStaticReflectivePresentations
        apply costStaticReflectivePresentationDecl_mem
        exact rhoReflectivePresentation_mem_source
      · rw [← sourceEquality, ← targetEquality]
        cases color <;>
          simp [rhoCalc, rhoReflectivePresentation, costStaticEquationDecl,
            costBaseEquationDecl, costWrappedEquationDecl, costBaseEquation,
            costWrappedEquation, mapEquationSchemaNames, mapEquation,
            mapPatternListSchemaNames, mapPatternSchemaNames, mapPattern,
            applyBindings, costStaticReflectivePresentationDecl,
            costBaseReflectivePresentationDecl,
            costWrappedReflectivePresentationDecl, mapReflectivePresentation,
            costBaseStaticReflectiveSymbols,
            costWrappedStaticReflectiveSymbols,
            costBaseLanguageDefSymbolMap, costBaseStaticSymbols,
            costWrappedStaticSymbols, costBaseConstructorName,
            costWrappedConstructorName, costBaseConstructorTag,
            costWrappedConstructorTag,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]
  | @reverse equation source target initialBindings finalBindings membership
      matched premises targetEquality =>
      have membership' : equation ∈ rhoCIGSLT.costStaticEquations := by
        change equation ∈ rhoCIGSLT.costStaticEquations at membership
        exact membership
      obtain ⟨color, sourceEquation, sourceMembership, equationEquality⟩ :=
        (mem_costStaticEquations_iff_exists_source rhoCIGSLT).1 membership'
      have sourceEquationEquality :
          sourceEquation = rhoCalc.equations[0] := by
        change sourceEquation ∈ [rhoCalc.equations[0]] at sourceMembership
        simpa using sourceMembership
      subst sourceEquation
      subst equation
      have premisesEmpty :
          (costStaticEquationDecl rhoCIGSLT color
            rhoCalc.equations[0]).premises = [] := by
        apply costStaticEquationDecl_premises
        rfl
      rw [premisesEmpty] at premises
      cases premises
      have matchCorrect :
          Pattern.isMatchCorrect
            (costStaticEquationDecl rhoCIGSLT color
              rhoCalc.equations[0]).right = true := by
        cases color <;> decide
      have sourceEquality := matchPattern_correct matched matchCorrect
      refine ⟨costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl, ?_, ?_⟩
      · change costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl ∈
            rhoCIGSLT.costStaticReflectivePresentations
        apply costStaticReflectivePresentationDecl_mem
        exact rhoReflectivePresentation_mem_source
      · rw [← sourceEquality, ← targetEquality]
        cases color <;>
          simp [rhoCalc, rhoReflectivePresentation, costStaticEquationDecl,
            costBaseEquationDecl, costWrappedEquationDecl, costBaseEquation,
            costWrappedEquation, mapEquationSchemaNames, mapEquation,
            mapPatternListSchemaNames, mapPatternSchemaNames, mapPattern,
            applyBindings, costStaticReflectivePresentationDecl,
            costBaseReflectivePresentationDecl,
            costWrappedReflectivePresentationDecl, mapReflectivePresentation,
            costBaseStaticReflectiveSymbols,
            costWrappedStaticReflectiveSymbols,
            costBaseLanguageDefSymbolMap, costBaseStaticSymbols,
            costWrappedStaticSymbols, costBaseConstructorName,
            costWrappedConstructorName, costBaseConstructorTag,
            costWrappedConstructorTag,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

/-- The generated ordinary rho equation table is natural under every
order-preserving ambient binder embedding.  Each equation instance is first
identified with its matching generated reflective edge, after which the
generic declaration-derived ambient-renaming theorem applies. -/
theorem rho_costDeclaredEquationAmbientRenamingStable :
    DeclaredEquationAmbientRenamingStable (profile := rhoCIGSLT.costWholeReflectionProfile) rhoCIGSLT.costWholeLanguage := by
  intro rename strict depth context redex contractum instanceWitness
  obtain ⟨fuel, bounded⟩ := instanceWitness
  obtain ⟨declaration, membership, representatives⟩ :=
    rho_costEquationInstanceAt_canonicalize_eq bounded
  exact (reflectiveEquationAmbientRenamingStable_of_validate_eq_nil
    (profile := rhoCIGSLT.costWholeReflectionProfile)
      rhoCIGSLT.costWholeLanguage rhoCIGSLT.costWholeLanguage_validate
        rhoCIGSLT.costWholeReflectionProfile_validate)
      rename strict depth context membership representatives

/-- Both ordinary and reflective generated rho equations are natural under
ambient binder embeddings, using only the generated language's own equation
and reflective declaration tables. -/
theorem rho_costSupportedEquationAmbientRenamingStable :
    SupportedEquationAmbientRenamingStable (profile := rhoCIGSLT.costWholeReflectionProfile)
      rhoCIGSLT.costWholeLanguage :=
  ⟨rho_costDeclaredEquationAmbientRenamingStable,
    reflectiveEquationAmbientRenamingStable_of_validate_eq_nil
      (profile := rhoCIGSLT.costWholeReflectionProfile)
      rhoCIGSLT.costWholeLanguage rhoCIGSLT.costWholeLanguage_validate
        rhoCIGSLT.costWholeReflectionProfile_validate⟩

/-- Every generated rho equation generator remains one generated equation
generator after an arbitrary ambient binder embedding.  Ordinary generated
QuoteDrop instances are first identified with their matching authored
reflective declaration, so both generator cases share the same reflective
factor theorem. -/
theorem rho_costEquationContextStepAmbientRenamingStable
    (rename : Nat → Nat) (depth : Nat) {left right : Pattern}
    (step : ReflectiveEquationSemantics.ReflectiveEquationContextStep rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right) :
    ReflectiveEquationSemantics.ReflectiveEquationContextStep rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage
      (ContextSubstitution.renameAmbientBVarsAt rename depth left)
      (ContextSubstitution.renameAmbientBVarsAt rename depth right) := by
  cases step with
  | core coreStep =>
      cases coreStep with
      | inContext context instanceWitness =>
          obtain ⟨fuel, bounded⟩ := instanceWitness
          obtain ⟨declaration, membership, representatives⟩ :=
            rho_costEquationInstanceAt_canonicalize_eq bounded
          exact
            reflectiveEquationContextStep_renameAmbientBVarsAt_of_validate_eq_nil
              (profile := rhoCIGSLT.costWholeReflectionProfile)
              rhoCIGSLT.costWholeLanguage
              rhoCIGSLT.costWholeLanguage_validate
              rhoCIGSLT.costWholeReflectionProfile_validate
              rename depth context membership representatives
  | reflectiveInContext context membership representatives =>
      exact
        reflectiveEquationContextStep_renameAmbientBVarsAt_of_validate_eq_nil
          (profile := rhoCIGSLT.costWholeReflectionProfile)
          rhoCIGSLT.costWholeLanguage rhoCIGSLT.costWholeLanguage_validate
          rhoCIGSLT.costWholeReflectionProfile_validate rename depth context
          membership representatives

/-- Root weakening is the affine specialization of generated-rho ambient
renaming, and therefore preserves one generator rather than merely its raw
equivalence class. -/
theorem rho_costEquationContextStepRootWeakeningStable :
    ReflectiveEquationContextStepRootWeakeningStable
      rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage := by
  intro left right step shift
  simpa only [ContextSubstitution.renameAmbientBVarsAt_add_eq_liftBVars] using
    rho_costEquationContextStepAmbientRenamingStable
      (fun index => index + shift) 0 step

/-- Typed generated-rho equation paths remain in their exact open fibre when
an arbitrary block of binders is inserted at the root. -/
theorem rho_costOpenPatternEquationWeakeningStable :
    ReflectiveOpenPatternEquationWeakeningStable
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage :=
  rho_costEquationContextStepRootWeakeningStable.toReflectiveOpenPattern

/-- Mapping one certified source generator into a selected Cost colour and
reinserting an arbitrary ambient binder thinning remains one edge of the
exact split typed target fibre.  Boundary substitution is deliberately not
performed here; its independent typed transport is the remaining action law. -/
theorem rho_costStaticMappedThickenedGeneratorFiberAction
    {color : CostStaticColor}
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : LangSort rhoCIGSLT.theory.presentation.presentation.language}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    {left right : CostStaticSourceTerm rhoCIGSLT color free support sourceBound
      targetBound sort}
    (generator : CostStaticSourceTerm.generator left right) :
    (AvailableOpenPattern.equationSetoid
      (profile := rhoCIGSLT.costWholeReflectionProfile)
      rhoCIGSLT.costWholeLanguage
      (free.map (color.symbols rhoCIGSLT)) targetBound []
        (.base (color.mapLangSort rhoCIGSLT sort).1)).r
      (left.mappedThickenedAvailable thinning)
      (right.mappedThickenedAvailable thinning) := by
  have mapped : ReflectiveEquationSemantics.ReflectiveEquationContextStep rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage
      (mapPattern (color.symbols rhoCIGSLT) left.term.1)
      (mapPattern (color.symbols rhoCIGSLT) right.term.1) := by
    apply equationContextStep_mapCostStatic rhoCIGSLT color
    exact generator
  have thickened := rho_costEquationContextStepAmbientRenamingStable
    thinning.toTargetIndex 0 mapped
  apply Relation.EqvGen.rel _ _
  change ReflectiveEquationSemantics.ReflectiveEquationContextStep rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage
      (left.mappedThickenedAvailable thinning).pattern
      (right.mappedThickenedAvailable thinning).pattern
  simpa only [CostStaticSourceTerm.mappedThickenedAvailable_pattern,
    CostStaticBinderThinning.thickenAmbientBVars_eq_renameAmbientBVarsAt]
    using thickened

/-- Every source-authored rho equation generator acts soundly after mapping
into one selected Cost colour, reinserting ambient binders, and restoring an
arbitrary supported finite boundary assignment.  The proof factors through
rho's sole canonical representative; no mixed-colour target generator is
assumed stable. -/
theorem rho_costStaticMappedGeneratorAction :
    CostStaticMappedGeneratorAction rhoCIGSLT := by
  intro color free assignmentFree targetFree support assignmentSupport
    sourceBound targetBound sort thinning assignment freeContext
      reflectiveSupport left right generator
  have leftEquivalent := rhoCostStaticActionAt_canonicalize_equationEquiv
    (inner := []) (available := targetBound) thinning assignment freeContext
      reflectiveSupport left.term.2.1.1 left.safe
        left.supported.constructorsWithin left.term.2.1.2.2.1
  have rightEquivalent := rhoCostStaticActionAt_canonicalize_equationEquiv
    (inner := []) (available := targetBound) thinning assignment freeContext
      reflectiveSupport right.term.2.1.1 right.safe
        right.supported.constructorsWithin right.term.2.1.2.2.1
  have sourceGenerator :
      ReflectiveEquationSemantics.ReflectiveEquationContextStep rhoReflectionProfile
        defaultBasePremises rhoCalc
        left.term.1 right.term.1 := by
    change ReflectiveEquationSemantics.ReflectiveEquationContextStep
      rhoCIGSLT.reflection.1 defaultBasePremises rhoCalc
        left.term.1 right.term.1 at generator
    simpa only [rhoCIGSLT_reflectionProfile_eq] using generator
  have canonicalEquality :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          rhoReflectivePresentation left.term.1 =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          rhoReflectivePresentation right.term.1 := by
    simpa only [CanonicalMatch.derivedCanonicalize_eq] using
      LanguageDefSemanticAgreement.rhoEquationContextStep_canonicalize_eq
        sourceGenerator
  rw [canonicalEquality] at leftEquivalent
  have combined := rhoCostEquationEquiv_trans leftEquivalent
    (Relation.EqvGen.symm _ _ rightEquivalent)
  simpa [CostStaticSourceTerm.act, rhoCostStaticActionAt,
    ReflectiveContextSupport.substitute] using combined

/-- Every source-authored rho generator acts by one selected generated
reflective edge after mapping, ambient thinning, and supported boundary
substitution.  Because the edge is built directly between the two certified
endpoints, every intermediate representative remains in the exact target
typing fibre. -/
theorem rho_costStaticMappedGeneratorFiberAction :
    CostStaticMappedGeneratorFiberAction rhoCIGSLT := by
  intro color free assignmentFree targetFree support assignmentSupport
    sourceBound targetBound sort thinning assignment freeContext
      reflectiveSupport left right generator
  have sourceGenerator :
      ReflectiveEquationSemantics.ReflectiveEquationContextStep rhoReflectionProfile
        defaultBasePremises rhoCalc
        left.term.1 right.term.1 := by
    change ReflectiveEquationSemantics.ReflectiveEquationContextStep
      rhoCIGSLT.reflection.1 defaultBasePremises rhoCalc
        left.term.1 right.term.1 at generator
    simpa only [rhoCIGSLT_reflectionProfile_eq] using generator
  have sourceCanonicalEquality :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          rhoReflectivePresentation left.term.1 =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          rhoReflectivePresentation right.term.1 := by
    simpa only [CanonicalMatch.derivedCanonicalize_eq] using
      LanguageDefSemanticAgreement.rhoEquationContextStep_canonicalize_eq
        sourceGenerator
  have representatives :=
    rhoCostStaticActionAt_canonicalize_eq_of_canonicalize_eq
      (inner := []) (available := targetBound) thinning assignment freeContext
        reflectiveSupport left.term.2.1.1 right.term.2.1.1 left.safe right.safe
        left.supported.constructorsWithin
        right.supported.constructorsWithin left.term.2.1.2.2.1
        right.term.2.1.2.2.1 sourceCanonicalEquality
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        rhoReflectivePresentation_mem_source
  have targetGenerator : ReflectiveEquationSemantics.ReflectiveEquationContextStep
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises rhoCIGSLT.costWholeLanguage
      (left.act thinning assignment) (right.act thinning assignment) := by
    apply ReflectiveEquationSemantics.ReflectiveEquationContextStep.reflectiveInContext .hole
      declarationMembership
    simpa [declaration, CostStaticSourceTerm.act, rhoCostStaticActionAt,
      ReflectiveContextSupport.substitute] using representatives
  have availableGenerator :
      WellSorted.AvailableOpenPattern.equationGenerator
        (left.actAvailable thinning assignment freeContext reflectiveSupport)
        (right.actAvailable thinning assignment freeContext
          reflectiveSupport) := by
    unfold WellSorted.AvailableOpenPattern.equationGenerator
    simpa only [CostStaticSourceTerm.actAvailable_pattern] using targetGenerator
  exact Relation.EqvGen.rel _ _ availableGenerator

/-- Rho's canonical path is a single authored reflective edge in every
constructor- and support-certified static source fibre.  Both endpoints are
the proof-relevant terms already carried by the region node; the edge adds no
parallel canonicalization authority. -/
theorem rho_costStaticCanonicalPathSafe :
    CostStaticCanonicalPathSafe rhoCIGSLT := by
  intro color targetFree node
  apply Relation.EqvGen.rel _ _
  unfold CostStaticSourceTerm.generator
  apply ReflectiveEquationSemantics.ReflectiveEquationContextStep.reflectiveInContext .hole
    (declaration :=
      rhoReflectivePresentation.toReflectivePresentationDecl)
  · change List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
      [rhoReflectivePresentation.toReflectivePresentationDecl]
    exact .head _
  · change
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          rhoReflectivePresentation
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
            node.skeleton.1) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          rhoReflectivePresentation node.skeleton.1
    rw [CanonicalMatch.derivedCanonicalize_eq,
      CanonicalMatch.derivedCanonicalize_eq]
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize_idempotent
        node.skeleton.1

/-- The exact typed unary normalization laws for the rho Cost construction.
Each field is discharged against the selected generated declaration and the
single generated `LanguageDef`; no mixed-colour stability assumption is used. -/
theorem rho_costTypedUnaryNormalizationLaws :
    Cost.SemanticSection.Laws rhoCIGSLT where
  mappedGeneratorFiberAction := rho_costStaticMappedGeneratorFiberAction
  weakeningStable := rho_costOpenPatternEquationWeakeningStable
  canonicalPathSafe := rho_costStaticCanonicalPathSafe

/-- Pure rho has at most one declaration-derived collection candidate in
every exact expected fiber.  Its only bare collection declaration is parallel
composition; direct homogeneous collections and bare constructors inhabit
different source result-type shapes. -/
theorem rho_costStaticCollectionUnambiguous
    (color : CostStaticColor)
    (targetFree : FreeTypeContext) (targetBound : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern)
    (expected : TypeExpr) :
    CostStaticCollectionUnambiguousAt rhoCIGSLT color targetFree targetBound
      collectionType elements expected := by
  unfold CostStaticCollectionUnambiguousAt
  unfold costStaticCollectionTypingChoices
  split
  · simp [CostCandidateFamilyUnambiguous]
  · rename_i sourceExpected decoded
    have sourceTerms :
        rhoCIGSLT.theory.presentation.presentation.language.terms =
          [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2],
            rhoCalc.terms[3], rhoCalc.terms[4], rhoCalc.terms[5]] := by
      rfl
    rw [sourceTerms]
    cases sourceExpected <;>
      simp [bareCostStaticCollectionTypingChoices,
        List.filterMap, CostCandidateFamilyUnambiguous, rhoCalc,
        WellSorted.bareCollectionElementType?, TypeExpr.name, TypeExpr.proc,
        TypeExpr.bag, TypeExpr.baseType]
    all_goals
      first
      | exact optionSingletonList_length_le_one _
      | exact ifSingletonList_length_le_one _ _

/-- Parallel composition is the sole authored rho declaration whose
representation is one bare collection. -/
theorem rho_rule_eq_parallel_of_bare_shape
    {rule : GrammarRule} (membership : rule ∈ rhoCalc.terms)
    {parameterName : String} {collectionType : CollType}
    {elementType : TypeExpr}
    (parameterShape : rule.params =
      [.simple parameterName (.collection collectionType elementType)]) :
    rule = rhoCalc.terms[3] := by
  change rule ∈ [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2],
    rhoCalc.terms[3], rhoCalc.terms[4], rhoCalc.terms[5]] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with first | second | third | fourth | fifth | sixth
  · subst rule
    simp [rhoCalc, TypeExpr.name, TypeExpr.proc, TypeExpr.bag,
      TypeExpr.baseType] at parameterShape
  · subst rule
    simp [rhoCalc, TypeExpr.name, TypeExpr.proc, TypeExpr.bag,
      TypeExpr.baseType] at parameterShape
  · subst rule
    simp [rhoCalc, TypeExpr.name, TypeExpr.proc, TypeExpr.bag,
      TypeExpr.baseType] at parameterShape
  · subst rule
    rfl
  · subst rule
    simp [rhoCalc, TypeExpr.name, TypeExpr.proc, TypeExpr.bag,
      TypeExpr.baseType] at parameterShape
  · subst rule
    simp [rhoCalc, TypeExpr.name, TypeExpr.proc, TypeExpr.bag,
      TypeExpr.baseType] at parameterShape

/-- A rho static plan rooted at a bare collection necessarily comes from the
authored PPar rule, hence its source result is the interacting process sort.
This is the node-level form used by cast-stable static-root comparisons; it
does not rerun the executable candidate search. -/
theorem rho_collection_node_sourceSort_interacting
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {collectionType : CollType} {elements : List Pattern}
    {rest : Option String}
    (shape : node.term.1 = .collection collectionType elements rest) :
    node.sourceSort.1 =
      rhoCIGSLT.theory.presentation.interactingSort.1.name := by
  obtain ⟨choice, selected⟩ :=
    node.plan.collection_choice_of_isStaticRoot node.rootStatic shape
  rcases mem_costStaticCollectionTypingChoices_sound rhoCIGSLT color
      targetFree node.targetBound collectionType elements
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base node.sourceSort.1)) choice selected with
    direct | bare
  · rcases direct with
      ⟨sourceElementType, _choiceShape, expectedEquality, _checked⟩
    have impossible :
        (.base node.sourceSort.1 : TypeExpr) =
          .collection collectionType sourceElementType :=
      mapTypeExpr_costStatic_injective rhoCIGSLT color expectedEquality
    cases impossible
  · rcases bare with
      ⟨rule, sourceElementType, _choiceShape, ruleMembership, _wrapped,
        expectedEquality, parameterName, parameterShape, _checked⟩
    have sourceTypeEquality :
        (.base node.sourceSort.1 : TypeExpr) = .base rule.category :=
      mapTypeExpr_costStatic_injective rhoCIGSLT color expectedEquality
    have sourceCategoryEquality : node.sourceSort.1 = rule.category :=
      TypeExpr.base.inj sourceTypeEquality
    have ruleEquality : rule = rhoCalc.terms[3] :=
      rho_rule_eq_parallel_of_bare_shape ruleMembership parameterShape
    have ruleCategory : rule.category = "Proc" := by
      rw [ruleEquality]
      rfl
    have nodeInteracting : node.sourceSort.1 = "Proc" :=
      sourceCategoryEquality.trans ruleCategory
    change node.sourceSort.1 = (TypeDecl.plain "Proc").name
    simpa [TypeDecl.plain] using nodeInteracting

/-- Any rho static root whose compact syntax is a bare collection is rooted
at the interacting process sort.  Direct homogeneous collection typing is
impossible at the node's authored base-sort index; the remaining declaration
choice is necessarily PPar. -/
private theorem rho_collection_root_sourceSort_interacting
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {term : OpenTerm rhoCIGSLT.costWholeLanguage targetFree targetBound
      targetSort}
    (candidate : CostStaticRootNode rhoCIGSLT targetFree targetBound targetSort
      term)
    {collectionType : CollType} {elements : List Pattern}
    {rest : Option String}
    (shape : term.1 = .collection collectionType elements rest) :
    candidate.sourceSort.1 =
      rhoCIGSLT.theory.presentation.interactingSort.1.name := by
  have nodeShape : candidate.node.term.1 =
      .collection collectionType elements rest :=
    candidate.nodeTerm_eq.trans shape
  have nodeInteracting :=
    rho_collection_node_sourceSort_interacting candidate.node nodeShape
  exact (congrArg Subtype.val candidate.nodeSourceSort_eq).symm.trans
    nodeInteracting

/-- Two rho collection roots in one compact target fibre select the same
static colour because PPar returns the distinguished interacting sort, whose
base and wrapped images are disjoint. -/
private theorem rho_color_eq_of_collection
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {term : OpenTerm rhoCIGSLT.costWholeLanguage targetFree targetBound
      targetSort}
    (first second : CostStaticRootNode rhoCIGSLT targetFree targetBound
      targetSort term)
    {collectionType : CollType} {elements : List Pattern}
    {rest : Option String}
    (shape : term.1 = .collection collectionType elements rest) :
    first.color = second.color := by
  exact CostStaticColor.color_eq_of_mapLangSort_eq_of_interacting rhoCIGSLT
    first.color second.color first.sourceSort second.sourceSort
    (rho_collection_root_sourceSort_interacting first shape)
    (rho_collection_root_sourceSort_interacting second shape)
    (first.targetSort_eq.trans second.targetSort_eq.symm)

/-- Every exact rho compact root fibre contains at most one proof-relevant
static decomposition candidate.  Application colours are fixed by intrinsic
wire decoding; collection colours are fixed by PPar's interacting result
sort. -/
theorem rho_costStaticRootUnambiguous
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : OpenTerm rhoCIGSLT.costWholeLanguage targetFree targetBound
      targetSort) :
    CostStaticRootNode.UnambiguousAt term := by
  apply costCandidateFamilyUnambiguous_of_nodup_of_mem_eq
    (CostStaticRootNode.buildCandidates_nodup term)
  intro first second firstMembership secondMembership
  rcases first.node.plan.pattern_shape_of_isStaticRoot first.node.rootStatic with
      ⟨wireName, arguments, firstShape⟩ |
      ⟨collectionType, elements, rest, firstShape⟩
  · have termShape : term.1 = .apply wireName arguments :=
      first.nodeTerm_eq.symm.trans firstShape
    exact CostStaticRootNode.eq_of_color_eq_of_mem_buildCandidates
      firstMembership secondMembership
      (CostStaticRootNode.color_eq_of_application first second termShape)
  · have termShape : term.1 =
        .collection collectionType elements rest :=
      first.nodeTerm_eq.symm.trans firstShape
    exact CostStaticRootNode.eq_of_color_eq_of_mem_buildCandidates
      firstMembership secondMembership
      (rho_color_eq_of_collection first second termShape)

/-- Pure rho satisfies the structural finite-candidate criterion used to
discharge exact cost layer canonical laws. -/
theorem rho_unambiguousStaticDecomposition :
    UnambiguousStaticDecomposition rhoCIGSLT where
  rootCandidates := rho_costStaticRootUnambiguous
  collectionCandidates := rho_costStaticCollectionUnambiguous

/-- Structural uniqueness discharges exact compact elaboration coherence for
pure rho: any two proof-relevant region trees for one admitted compact term
erase to the same child-first normal form. -/
theorem rho_compactCostNormalizationCoherent :
    CompactCostNormalizationCoherent rhoCIGSLT :=
  rho_unambiguousStaticDecomposition.compactCoherent

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
