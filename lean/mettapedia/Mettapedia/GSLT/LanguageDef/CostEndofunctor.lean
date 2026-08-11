import Mettapedia.GSLT.LanguageDef.CostContinued
import Mettapedia.GSLT.LanguageDef.CostGeneratorHereditaryAlignment
import Mettapedia.GSLT.LanguageDef.CostSemanticErasure
import Mettapedia.OSLF.MeTTaIL.PatternCode

/-!
# Endofunctor closure of the declaration-derived Cost construction

Repeated Cost application retypes an already wrapped interaction.  The old
wrapped carrier maps to the new wrapped carrier; every other old sort enters
the next tagged base fiber.  The retained program and environment
introductions receive base copies, while every other constructor receives a
wrapped copy.  This profile-sensitive distinction is derived from the ordered
interaction cut and is not an execution policy.
-/

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open StructuralMorphism
open WellSorted
open ContinuationRetypingPlan

namespace CIGSLT

mutual
  /-- Renaming schema-local names leaves the visible constructor fragment
  unchanged. -/
  theorem constructorsWithin_mapPatternSchemaNames
      {allowed : String → Prop} (mapName : String → String)
      {pattern : Pattern} (supported : ConstructorsWithin allowed pattern) :
      ConstructorsWithin allowed (mapPatternSchemaNames mapName pattern) := by
    induction pattern using Pattern.inductionOn with
    | hbvar index => trivial
    | hfvar name => trivial
    | happly constructor arguments inductionHypothesis =>
        simpa [mapPatternSchemaNames, mapPatternListSchemaNames_eq_map] using
          And.intro supported.1
            (constructorListWithin_mapPatternSchemaNames mapName supported.2
              inductionHypothesis)
    | hlambda binder body inductionHypothesis =>
        exact inductionHypothesis supported
    | hmultiLambda arity binders body inductionHypothesis =>
        exact inductionHypothesis supported
    | hsubst body replacement bodyInduction replacementInduction =>
        exact ⟨bodyInduction supported.1, replacementInduction supported.2⟩
    | hcollection collectionType elements rest inductionHypothesis =>
        simpa [mapPatternSchemaNames,
          mapPatternListSchemaNames_eq_map] using
            constructorListWithin_mapPatternSchemaNames mapName supported
              inductionHypothesis

  /-- List companion to `constructorsWithin_mapPatternSchemaNames`. -/
  theorem constructorListWithin_mapPatternSchemaNames
      {allowed : String → Prop} (mapName : String → String)
      {patterns : List Pattern}
      (supported : ConstructorListWithin allowed patterns)
      (inductionHypothesis : ∀ pattern ∈ patterns,
        ConstructorsWithin allowed pattern →
          ConstructorsWithin allowed
            (mapPatternSchemaNames mapName pattern)) :
      ConstructorListWithin allowed
        (patterns.map (mapPatternSchemaNames mapName)) := by
    rw [constructorListWithin_iff_forall]
    intro mapped membership
    rcases List.mem_map.mp membership with ⟨pattern, sourceMembership, rfl⟩
    exact inductionHypothesis pattern sourceMembership
      (supported.of_mem sourceMembership)
end

/-- Sort action used to close a generated Cost interaction under another
Cost application. -/
def costClosureSortName (_source : CIGSLT) (sort : String) : String :=
  if sort = costWrappedSortName then costWrappedSortName
  else costBaseSortName sort

/-- Constructor action for a second Cost layer.  The two ordered
introductions stay in the base fiber; all other constructors receive wrapped
copies so continuation-bearing arguments are transformed hereditarily. -/
def costClosureConstructorName (source : CIGSLT) (constructor : String) :
    String :=
  if constructor = source.costInteractionCut.program.constructor.1.label ∨
      constructor =
        source.costInteractionCut.environment.constructor.1.label then
    costBaseConstructorName constructor
  else
    costWrappedConstructorName constructor

/-- Total symbol action underlying repeated Cost retyping. -/
def costClosureSymbols (source : CIGSLT) : PresentationSymbols where
  sort := source.costClosureSortName
  constructor := source.costClosureConstructorName
  relation := id
  equation := id
  rewrite := id

/-- Negative canary for a tempting but false uniform-transport proof:
closure retyping sends the non-principal signed apparatus to the wrapped
constructor fiber, whereas redex retyping needs its next base copy. -/
theorem costClosureConstructorName_signed_ne_base (source : CIGSLT) :
    source.costClosureConstructorName costSignedConstructorName ≠
      costBaseConstructorName costSignedConstructorName := by
  have notProgram :
      costSignedConstructorName ≠
        source.costInteractionCut.program.constructor.1.label := by
    rw [source.costInteractionCut_program_constructor]
    exact (costBaseConstructorName_ne_apparatus
      source.cut.program.constructor.1.label "signed").symm
  have notEnvironment :
      costSignedConstructorName ≠
        source.costInteractionCut.environment.constructor.1.label := by
    rw [source.costInteractionCut_environment_constructor]
    exact (costBaseConstructorName_ne_apparatus
      source.cut.environment.constructor.1.label "signed").symm
  rw [costClosureConstructorName]
  simp only [notProgram, notEnvironment, false_or, if_false]
  exact (costBaseConstructorName_ne_wrapped _ _).symm

@[simp]
theorem costClosureSortName_wrapped (source : CIGSLT) :
    source.costClosureSortName costWrappedSortName = costWrappedSortName := by
  simp [costClosureSortName]

theorem costClosureSortName_of_ne (source : CIGSLT) (sort : String)
    (inequality : sort ≠ costWrappedSortName) :
    source.costClosureSortName sort = costBaseSortName sort := by
  simp [costClosureSortName, inequality]

@[simp]
theorem mapTypeExpr_costClosureSymbols (source : CIGSLT)
    (type : TypeExpr) :
    mapTypeExpr source.costClosureSymbols type =
      costWrappedTypeExpr costWrappedSortName type := by
  induction type with
  | base sort =>
      by_cases equality : sort = costWrappedSortName <;>
        simp [costClosureSymbols, costClosureSortName,
          costWrappedTypeExpr, mapTypeExpr, equality]
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      simp [mapTypeExpr, costWrappedTypeExpr, domainHypothesis,
        codomainHypothesis]
  | multiBinder body inductionHypothesis =>
      simp [mapTypeExpr, costWrappedTypeExpr, inductionHypothesis]
  | collection collectionType body inductionHypothesis =>
      simp [mapTypeExpr, costWrappedTypeExpr, inductionHypothesis]

@[simp]
theorem mapTermParam_costClosureSymbols (source : CIGSLT)
    (parameter : TermParam) :
    mapTermParam source.costClosureSymbols parameter =
      mapParameterType (costWrappedTypeExpr costWrappedSortName) parameter := by
  cases parameter <;>
    simp [mapTermParam, mapParameterType,
      source.mapTypeExpr_costClosureSymbols]

/-- Closing an already-base-tagged sort adds exactly one further base tag.
This is the non-interacting branch of repeated Cost retyping. -/
@[simp]
theorem costClosureSortName_costBaseSortName (source : CIGSLT)
    (sort : String) :
    source.costClosureSortName (costBaseSortName sort) =
      costBaseSortName (costBaseSortName sort) := by
  exact source.costClosureSortName_of_ne _
    (costBaseSortName_ne_wrapped sort)

/-- Wrapping a base-tagged type at the next Cost layer agrees with applying
the base type action twice. -/
@[simp]
theorem costWrappedTypeExpr_wrapped_costBaseTypeExpr (type : TypeExpr) :
    costWrappedTypeExpr costWrappedSortName (costBaseTypeExpr type) =
      costBaseTypeExpr (costBaseTypeExpr type) := by
  induction type <;>
    simp_all [costWrappedTypeExpr, costBaseTypeExpr,
      costBaseSortName_ne_wrapped]

/-- Away from the distinguished wrapped carrier, the closure action sends
one complete type declaration to its next tagged base copy. -/
theorem mapTypeDecl_costClosure_of_ne (source : CIGSLT)
    (declaration : TypeDecl)
    (inequality : declaration.name ≠ costWrappedSortName) :
    mapTypeDecl source.costClosureSymbols declaration =
      { declaration with name := costBaseSortName declaration.name } := by
  cases declaration
  simp [mapTypeDecl, costClosureSymbols, costClosureSortName, inequality]

/-- The distinguished wrapped carrier is stable under repeated Cost
retyping. -/
@[simp]
theorem mapTypeDecl_costClosure_wrapped (source : CIGSLT) :
    mapTypeDecl source.costClosureSymbols
        (TypeDecl.plain costWrappedSortName) =
      TypeDecl.plain costWrappedSortName := by
  simp [mapTypeDecl, costClosureSymbols, costClosureSortName, TypeDecl.plain]

/-- Every type declaration in the complete Cost language maps into the exact
next-layer continuation signature.  Base, wrapped, and fixed apparatus
declarations are kept distinct in the proof. -/
theorem mapTypeDecl_costClosure_mem_generated
    (source : CIGSLT) (declaration : TypeDecl)
    (membership :
      List.Mem declaration source.costWholeLanguage.types) :
    List.Mem (mapTypeDecl source.costClosureSymbols declaration)
      source.costContinuationRetyping.generatedLanguage.types := by
  have wholeMembership := membership
  change List.Mem declaration
      (source.continuationRetyping.generatedLanguage.types ++ costCoreTypes)
    at membership
  change List.Mem (mapTypeDecl source.costClosureSymbols declaration)
      ((source.costWholeLanguage.types.map fun entry =>
          { entry with name := costBaseSortName entry.name }) ++
        [TypeDecl.plain costWrappedSortName])
  rcases List.mem_append.mp membership with
    generatedMembership | apparatusMembership
  · change List.Mem declaration
        ((source.theory.presentation.presentation.language.types.map
            fun entry =>
              { entry with name := costBaseSortName entry.name }) ++
          [TypeDecl.plain costWrappedSortName]) at generatedMembership
    rcases List.mem_append.mp generatedMembership with
      baseMembership | wrappedMembership
    · rcases List.mem_map.mp baseMembership with
        ⟨sourceDeclaration, _sourceMembership, rfl⟩
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨{ sourceDeclaration with
          name := costBaseSortName sourceDeclaration.name }, ?_, ?_⟩
      · exact wholeMembership
      · exact (source.mapTypeDecl_costClosure_of_ne _
          (costBaseSortName_ne_wrapped sourceDeclaration.name)).symm
    · have equality :
          declaration = TypeDecl.plain costWrappedSortName :=
        List.mem_singleton.mp wrappedMembership
      subst declaration
      exact List.mem_append_right _ (by simp)
  · rcases List.mem_map.mp apparatusMembership with
      ⟨suffix, _suffixMembership, rfl⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨TypeDecl.plain (costApparatusSortName suffix), ?_, ?_⟩
    · exact wholeMembership
    · exact (source.mapTypeDecl_costClosure_of_ne _ fun equality =>
        costWrappedSortName_ne_apparatus suffix equality.symm).symm

/-- The closure symbol action commutes with the proof-relevant parameter
retyping of a retained base constructor.  Selection at the second layer is
the same indexed selection as at the first layer. -/
theorem mapTermParam_costClosure_costBaseParameter
    (source : CIGSLT) (rule : GrammarRule)
    (membership :
      rule ∈ source.theory.presentation.presentation.language.terms)
    (parameter : TermParam) (index : Nat) :
    mapTermParam source.costClosureSymbols
        (costBaseParameter source.cut rule (parameter, index)) =
      costBaseParameter source.costInteractionCut
        (costBaseConstructor source.cut rule)
        (costBaseParameter source.cut rule (parameter, index), index) := by
  unfold costBaseParameter
  rw [source.isSelectedContinuation_costBase rule membership index]
  split
  · change
      mapTermParam source.costClosureSymbols
          (mapParameterType
            (costWrappedTypeExpr
              source.theory.presentation.interactingSort.1.name) parameter) =
        mapParameterType
          (costWrappedTypeExpr costWrappedSortName)
          (mapParameterType
            (costWrappedTypeExpr
              source.theory.presentation.interactingSort.1.name) parameter)
    cases parameter <;>
      simp [mapTermParam, mapParameterType,
        source.mapTypeExpr_costClosureSymbols]
  · change
      mapTermParam source.costClosureSymbols
          (mapParameterType costBaseTypeExpr parameter) =
        mapParameterType costBaseTypeExpr
          (mapParameterType costBaseTypeExpr parameter)
    cases parameter <;>
      simp [mapTermParam, mapParameterType,
        source.mapTypeExpr_costClosureSymbols,
        costWrappedTypeExpr_wrapped_costBaseTypeExpr]

/-- Listwise form of
`mapTermParam_costClosure_costBaseParameter`. -/
@[simp]
theorem map_costClosure_costBaseConstructor_params
    (source : CIGSLT) (rule : GrammarRule)
    (membership :
      rule ∈ source.theory.presentation.presentation.language.terms) :
    (costBaseConstructor source.cut rule).params.map
        (mapTermParam source.costClosureSymbols) =
      (costBaseConstructor source.costInteractionCut
        (costBaseConstructor source.cut rule)).params := by
  apply List.ext_getElem
  · simp
  · intro index leftBounds rightBounds
    have sourceBounds : index < rule.params.length := by
      simpa using leftBounds
    rw [List.getElem_map]
    rw [costBaseConstructor_parameter source.costInteractionCut
      (costBaseConstructor source.cut rule) index (by
        simpa using rightBounds)]
    rw [costBaseConstructor_parameter source.cut rule index sourceBounds]
    exact source.mapTermParam_costClosure_costBaseParameter
      rule membership (rule.params[index]'(sourceBounds)) index

theorem costClosureConstructorName_of_nonprincipal (source : CIGSLT)
    (constructor : GrammarRule)
    (notProgram : constructor.label ≠
      source.costInteractionCut.program.constructor.1.label)
    (notEnvironment : constructor.label ≠
      source.costInteractionCut.environment.constructor.1.label) :
    source.costClosureConstructorName constructor.label =
      costWrappedConstructorName constructor.label := by
  unfold costClosureConstructorName
  rw [if_neg]
  exact fun equality => equality.elim notProgram notEnvironment

@[simp]
theorem costClosureConstructorName_program (source : CIGSLT) :
    source.costClosureConstructorName
      source.costInteractionCut.program.constructor.1.label =
      costBaseConstructorName
        source.costInteractionCut.program.constructor.1.label := by
  simp [costClosureConstructorName]

@[simp]
theorem costClosureConstructorName_environment (source : CIGSLT) :
    source.costClosureConstructorName
      source.costInteractionCut.environment.constructor.1.label =
      costBaseConstructorName
        source.costInteractionCut.environment.constructor.1.label := by
  simp [costClosureConstructorName]

/-- A retained program or environment introduction maps to its exact base
copy at the next Cost layer. -/
@[simp]
theorem mapGrammarRule_costClosure_costBaseConstructor_of_principal
    (source : CIGSLT) (rule : GrammarRule)
    (membership :
      rule ∈ source.theory.presentation.presentation.language.terms)
    (principal :
      costBaseConstructor source.cut rule =
          source.costInteractionCut.program.constructor.1 ∨
        costBaseConstructor source.cut rule =
          source.costInteractionCut.environment.constructor.1) :
    mapGrammarRule source.costClosureSymbols
        (costBaseConstructor source.cut rule) =
      costBaseConstructor source.costInteractionCut
        (costBaseConstructor source.cut rule) := by
  have parametersMap := source.map_costClosure_costBaseConstructor_params
    rule membership
  have labelMap :
      source.costClosureConstructorName
          (costBaseConstructor source.cut rule).label =
        costBaseConstructorName
          (costBaseConstructor source.cut rule).label := by
    rcases principal with program | environment
    · rw [program]
      exact source.costClosureConstructorName_program
    · rw [environment]
      exact source.costClosureConstructorName_environment
  cases rule with
  | mk label category parameters syntaxPattern evalPolicy =>
      change
        ({ label := source.costClosureConstructorName
              (costBaseConstructor source.cut
                ⟨label, category, parameters, syntaxPattern,
                  evalPolicy⟩).label
           category := source.costClosureSortName
              (costBaseConstructor source.cut
                ⟨label, category, parameters, syntaxPattern,
                  evalPolicy⟩).category
           params := (costBaseConstructor source.cut
              ⟨label, category, parameters, syntaxPattern,
                evalPolicy⟩).params.map
                (mapTermParam source.costClosureSymbols)
           syntaxPattern := (costBaseConstructor source.cut
              ⟨label, category, parameters, syntaxPattern,
                evalPolicy⟩).syntaxPattern
           evalPolicy? := (costBaseConstructor source.cut
              ⟨label, category, parameters, syntaxPattern,
                evalPolicy⟩).evalPolicy? } : GrammarRule) =
          costBaseConstructor source.costInteractionCut
            (costBaseConstructor source.cut
              ⟨label, category, parameters, syntaxPattern,
                evalPolicy⟩)
      rw [labelMap, parametersMap]
      rfl

/-- The retained program introduction maps to its exact next-layer base
copy. -/
@[simp]
theorem mapGrammarRule_costClosure_program (source : CIGSLT) :
    mapGrammarRule source.costClosureSymbols
        source.costInteractionCut.program.constructor.1 =
      costBaseConstructor source.costInteractionCut
        source.costInteractionCut.program.constructor.1 := by
  have equality :
      source.costInteractionCut.program.constructor.1 =
        costBaseConstructor source.cut source.cut.program.constructor.1 :=
    congrArg Subtype.val source.costInteractionCut_program_constructor
  rw [equality]
  exact source.mapGrammarRule_costClosure_costBaseConstructor_of_principal
    source.cut.program.constructor.1 source.cut.program.constructor.2
      (Or.inl equality.symm)

/-- The retained environment introduction maps to its exact next-layer base
copy. -/
@[simp]
theorem mapGrammarRule_costClosure_environment (source : CIGSLT) :
    mapGrammarRule source.costClosureSymbols
        source.costInteractionCut.environment.constructor.1 =
      costBaseConstructor source.costInteractionCut
        source.costInteractionCut.environment.constructor.1 := by
  have equality :
      source.costInteractionCut.environment.constructor.1 =
        costBaseConstructor source.cut
          source.cut.environment.constructor.1 :=
    congrArg Subtype.val source.costInteractionCut_environment_constructor
  rw [equality]
  exact source.mapGrammarRule_costClosure_costBaseConstructor_of_principal
    source.cut.environment.constructor.1
      source.cut.environment.constructor.2 (Or.inr equality.symm)

theorem costClosureConstructorName_of_nonprincipalAuthored
    (source : CIGSLT)
    (constructor :
      AuthoredConstructor source.costIGSLT.presentation.presentation)
    (notProgram : constructor ≠
      source.costInteractionCut.program.constructor)
    (notEnvironment : constructor ≠
      source.costInteractionCut.environment.constructor) :
    source.costClosureConstructorName constructor.1.label =
      costWrappedConstructorName constructor.1.label := by
  apply source.costClosureConstructorName_of_nonprincipal
  · intro equality
    exact notProgram
      (ContinuationRetypingPlan.authoredConstructorLabel_injective
        source.costIGSLT.presentation.presentation equality)
  · intro equality
    exact notEnvironment
      (ContinuationRetypingPlan.authoredConstructorLabel_injective
        source.costIGSLT.presentation.presentation equality)

theorem costCoreTerm_evalPolicy_eq_none (source : CIGSLT)
    (term : GrammarRule) (membership : term ∈ source.costCoreLanguage.terms) :
    term.evalPolicy? = none := by
  simp only [costCoreLanguage, List.mem_append] at membership
  rcases membership with generatedMembership | apparatusMembership
  · simp only [ContinuationRetypingPlan.generatedLanguage,
      List.mem_append] at generatedMembership
    rcases generatedMembership with baseMembership | wrappedMembership
    · rcases List.mem_map.mp baseMembership with
        ⟨constructor, _constructorMembership, rfl⟩
      rfl
    · rcases List.mem_map.mp wrappedMembership with
        ⟨constructor, _constructorMembership, rfl⟩
      rfl
  · simp only [costCoreConstructors, List.mem_cons, List.not_mem_nil,
      or_false] at apparatusMembership
    rcases apparatusMembership with equality | equality | equality | equality |
      equality | equality | equality <;> subst term <;> rfl

/-- Every non-principal declaration maps to the exact wrapped copy selected
by the next continuation plan. -/
theorem mapGrammarRule_costClosure_of_nonprincipal (source : CIGSLT)
    (constructor :
      AuthoredConstructor source.costIGSLT.presentation.presentation)
    (notProgram : constructor ≠
      source.costInteractionCut.program.constructor)
    (notEnvironment : constructor ≠
      source.costInteractionCut.environment.constructor) :
    mapGrammarRule source.costClosureSymbols constructor.1 =
      costWrappedConstructor (theory := source.costIGSLT) constructor.1 := by
  have labelMap := source.costClosureConstructorName_of_nonprincipalAuthored
    constructor notProgram notEnvironment
  have syntaxPattern := costCoreTerm_syntaxPattern_eq_nil source constructor.1
    (by exact constructor.2)
  have evalPolicy := source.costCoreTerm_evalPolicy_eq_none constructor.1
    (by exact constructor.2)
  rcases constructor with ⟨⟨label, category, parameters, syntaxItems,
    policy⟩, membership⟩
  simp only at labelMap syntaxPattern evalPolicy
  have parametersMap :
      parameters.map (mapTermParam source.costClosureSymbols) =
        parameters.map
          (mapParameterType (costWrappedTypeExpr costWrappedSortName)) := by
    apply List.map_congr_left
    intro parameter _membership
    exact source.mapTermParam_costClosureSymbols parameter
  change
    ({ label := source.costClosureConstructorName label
       category := source.costClosureSortName category
       params := parameters.map (mapTermParam source.costClosureSymbols)
       syntaxPattern := syntaxItems
       evalPolicy? := policy } : GrammarRule) =
      { label := costWrappedConstructorName label
        category := if category = costWrappedSortName then
          costWrappedSortName else costBaseSortName category
        params := parameters.map
          (mapParameterType (costWrappedTypeExpr costWrappedSortName))
        syntaxPattern := []
        evalPolicy? := none }
  rw [labelMap, parametersMap, syntaxPattern, evalPolicy]
  rfl

/-- Every complete Cost constructor maps into the exact next continuation
signature: the two retained introductions use base copies, and every other
constructor uses the hereditary wrapped copy. -/
theorem mapGrammarRule_costClosure_mem_generated
    (source : CIGSLT) (rule : GrammarRule)
    (membership : rule ∈ source.costWholeLanguage.terms) :
    mapGrammarRule source.costClosureSymbols rule ∈
      source.costContinuationRetyping.generatedLanguage.terms := by
  let authored :
      AuthoredConstructor source.costIGSLT.presentation.presentation :=
    ⟨rule, membership⟩
  by_cases program :
      authored = source.costInteractionCut.program.constructor
  · have ruleEquality := congrArg Subtype.val program
    change rule =
      source.costInteractionCut.program.constructor.1 at ruleEquality
    rw [ruleEquality, source.mapGrammarRule_costClosure_program]
    exact source.costContinuationRetyping.costBaseConstructor_mem_generated
      source.costInteractionCut.program.constructor.1
        source.costInteractionCut.program.constructor.2
  · by_cases environment :
        authored = source.costInteractionCut.environment.constructor
    · have ruleEquality := congrArg Subtype.val environment
      change rule =
        source.costInteractionCut.environment.constructor.1 at ruleEquality
      rw [ruleEquality, source.mapGrammarRule_costClosure_environment]
      exact source.costContinuationRetyping.costBaseConstructor_mem_generated
        source.costInteractionCut.environment.constructor.1
          source.costInteractionCut.environment.constructor.2
    · change mapGrammarRule source.costClosureSymbols authored.1 ∈
        source.costContinuationRetyping.generatedLanguage.terms
      rw [source.mapGrammarRule_costClosure_of_nonprincipal authored
        program environment]
      exact
        source.costContinuationRetyping.costWrappedConstructor_mem_generated
          authored
            ((source.costContinuationRetyping.mem_wrappedConstructors_iff
              authored).2 ⟨program, environment⟩)

/-- Repeated Cost has a single declaration-derived typing map from the
complete current language into the exact signature used to validate the next
layer.  This map is reusable by redex, contractum, and reflective retyping
proofs. -/
def costClosureTyping (source : CIGSLT) :
    TypingMorphism source.costWholePresentation
      source.costContinuationRetyping.generatedPresentation where
  symbols := source.costClosureSymbols
  mapsTypes declaration membership :=
    source.mapTypeDecl_costClosure_mem_generated declaration membership
  mapsTerms rule membership := by
    refine ⟨mapGrammarRule source.costClosureSymbols rule,
      source.mapGrammarRule_costClosure_mem_generated rule membership,
      ?_, ?_, ?_⟩ <;> rfl

/-- On every authored constructor, the finite wrapped-label choice used by
the next contractum translation is exactly the closure constructor action.
Unknown raw labels are deliberately outside this statement. -/
theorem costClosureConstructorChoice
    (source : CIGSLT) (rule : GrammarRule)
    (membership : rule ∈ source.costWholeLanguage.terms) :
    (if rule.label ∈ source.costContinuationRetyping.wrappedLabels then
        costWrappedConstructorName rule.label
      else costBaseConstructorName rule.label) =
      source.costClosureConstructorName rule.label := by
  let authored :
      AuthoredConstructor source.costIGSLT.presentation.presentation :=
    ⟨rule, membership⟩
  by_cases program :
      authored = source.costInteractionCut.program.constructor
  · have ruleEquality := congrArg Subtype.val program
    change rule =
      source.costInteractionCut.program.constructor.1 at ruleEquality
    have notWrapped :
        rule.label ∉ source.costContinuationRetyping.wrappedLabels := by
      change authored.1.label ∉
        source.costContinuationRetyping.wrappedLabels
      intro labelMembership
      have wrapped :=
        (source.costContinuationRetyping.mem_wrappedLabels_iff authored).1
          labelMembership
      exact
        ((source.costContinuationRetyping.mem_wrappedConstructors_iff
          authored).1 wrapped).1 program
    rw [if_neg notWrapped, ruleEquality]
    exact source.costClosureConstructorName_program.symm
  · by_cases environment :
        authored = source.costInteractionCut.environment.constructor
    · have ruleEquality := congrArg Subtype.val environment
      change rule =
        source.costInteractionCut.environment.constructor.1 at ruleEquality
      have notWrapped :
          rule.label ∉ source.costContinuationRetyping.wrappedLabels := by
        change authored.1.label ∉
          source.costContinuationRetyping.wrappedLabels
        intro labelMembership
        have wrapped :=
          (source.costContinuationRetyping.mem_wrappedLabels_iff authored).1
            labelMembership
        exact
          ((source.costContinuationRetyping.mem_wrappedConstructors_iff
            authored).1 wrapped).2 environment
      rw [if_neg notWrapped, ruleEquality]
      exact source.costClosureConstructorName_environment.symm
    · have wrapped :
          rule.label ∈ source.costContinuationRetyping.wrappedLabels := by
        change authored.1.label ∈
          source.costContinuationRetyping.wrappedLabels
        rw [source.costContinuationRetyping.mem_wrappedLabels_iff]
        exact
          (source.costContinuationRetyping.mem_wrappedConstructors_iff
            authored).2 ⟨program, environment⟩
      rw [if_pos wrapped]
      exact
        (source.costClosureConstructorName_of_nonprincipalAuthored
          authored program environment).symm

mutual
  /-- On a well-sorted term, next-layer contractum translation is exactly
  the total closure symbol action.  Typing supplies the declaration witness
  needed to exclude the unknown-label counterexample. -/
  theorem mapContractum_eq_mapPattern_of_hasType
      {source : CIGSLT}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed :
        HasType source.costWholeLanguage free bound pattern type) :
      source.costContinuationRetyping.mapContractum pattern =
        mapPattern source.costClosureSymbols pattern := by
    cases typed with
    | bvar lookup => rfl
    | fvar lookup => rfl
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        simp only [ContinuationRetypingPlan.mapContractum, mapPattern]
        rw [mapContractumList_eq_mapPattern_of_arguments argumentsTyped]
        rw [source.costClosureConstructorChoice rule membership]
        simp only [costClosureSymbols, mapPatternList_eq_map]
    | lambda bodyTyped =>
        simp only [ContinuationRetypingPlan.mapContractum, mapPattern]
        rw [mapContractum_eq_mapPattern_of_hasType bodyTyped]
    | multiLambda bodyTyped =>
        simp only [ContinuationRetypingPlan.mapContractum, mapPattern]
        rw [mapContractum_eq_mapPattern_of_hasType bodyTyped]
    | subst bodyTyped replacementTyped =>
        simp only [ContinuationRetypingPlan.mapContractum, mapPattern]
        rw [mapContractum_eq_mapPattern_of_hasType bodyTyped,
          mapContractum_eq_mapPattern_of_hasType replacementTyped]
    | collection elementsTyped =>
        simp only [ContinuationRetypingPlan.mapContractum, mapPattern]
        rw [mapContractumList_eq_mapPattern_of_elements elementsTyped]
        simp only [mapPatternList_eq_map]
    | collectionConstructor membership shape elementsTyped =>
        simp only [ContinuationRetypingPlan.mapContractum, mapPattern]
        rw [mapContractumList_eq_mapPattern_of_elements elementsTyped]
        simp only [mapPatternList_eq_map]

  /-- Ordered-argument companion to
  `mapContractum_eq_mapPattern_of_hasType`. -/
  theorem mapContractumList_eq_mapPattern_of_arguments
      {source : CIGSLT}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed :
        ArgumentsHaveTypes source.costWholeLanguage free bound
          arguments parameters) :
      source.costContinuationRetyping.mapContractumList arguments =
        arguments.map (mapPattern source.costClosureSymbols) := by
    cases typed with
    | nil => rfl
    | cons representation parameterType argumentTyped argumentsTyped =>
        simp only [ContinuationRetypingPlan.mapContractumList,
          List.map_cons]
        rw [mapContractum_eq_mapPattern_of_hasType argumentTyped,
          mapContractumList_eq_mapPattern_of_arguments argumentsTyped]

  /-- Collection-element companion to
  `mapContractum_eq_mapPattern_of_hasType`. -/
  theorem mapContractumList_eq_mapPattern_of_elements
      {source : CIGSLT}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed :
        ElementsHaveType source.costWholeLanguage free bound
          elements elementType) :
      source.costContinuationRetyping.mapContractumList elements =
        elements.map (mapPattern source.costClosureSymbols) := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp only [ContinuationRetypingPlan.mapContractumList,
          List.map_cons]
        rw [mapContractum_eq_mapPattern_of_hasType elementTyped,
          mapContractumList_eq_mapPattern_of_elements elementsTyped]
end

/-- On a transported source metavariable, closure-mapping the current
whole-redex context agrees with the next continuation plan's exact generated
context. -/
theorem costClosureMappedFreeContext_source
    (source : CIGSLT) (name : String) :
    (source.costWholeRedexFreeContext.map source.costClosureSymbols)
        (costSourceSchemaName name) =
      source.costContinuationRetyping.generatedFreeContext
        (costSourceSchemaName name) := by
  change Option.map (mapTypeExpr source.costClosureSymbols)
      (lookupTypeContext source.costWholeRedexTypeContext
        (costSourceSchemaName name)) =
    Option.map
      (fun type =>
        if costSourceSchemaName name =
              source.costInteractionCut.program.continuationVariable.name ∨
            costSourceSchemaName name =
              source.costInteractionCut.environment.continuationVariable.name
        then costWrappedTypeExpr costWrappedSortName type
        else costBaseTypeExpr type)
      (lookupTypeContext source.costWholeRedexTypeContext
        (costSourceSchemaName name))
  rw [source.costInteractionCut_program_continuationVariable_name,
    source.costInteractionCut_environment_continuationVariable_name]
  rw [CIGSLT.costWholeRedexTypeContext, lookupTypeContext_append,
    source.lookup_costRetypedSourceContext]
  unfold ContinuationRetypingPlan.generatedFreeContext
  generalize lookup : lookupTypeContext
    source.theory.presentation.interactionRewrite.1.typeContext name = found
  cases found with
  | none =>
      have notSignature :
          source.costSignatureVariable ≠ costSourceSchemaName name :=
        (source.costSourceSchemaName_ne_signature name).symm
      have notStackTail :
          source.costStackTailVariable ≠ costSourceSchemaName name :=
        (source.costSourceSchemaName_ne_stackTail name).symm
      simp [lookupTypeContext, notSignature, notStackTail]
  | some type =>
      by_cases program :
          name = source.cut.program.continuationVariable.name
      · subst name
        simp [source.mapTypeExpr_costClosureSymbols]
      · by_cases environment :
            name = source.cut.environment.continuationVariable.name
        · subst name
          simp [source.mapTypeExpr_costClosureSymbols]
        · simp [program, environment,
            costSourceSchemaName_injective.eq_iff,
            source.mapTypeExpr_costClosureSymbols,
            CIGSLT.costWrappedTypeExpr_wrapped_costBaseTypeExpr]

/-- The generated signature variable remains outside the continuation slots
and is base-tagged again at the next Cost layer. -/
theorem costClosureMappedFreeContext_signature (source : CIGSLT) :
    (source.costWholeRedexFreeContext.map source.costClosureSymbols)
        source.costSignatureVariable =
      source.costContinuationRetyping.generatedFreeContext
        source.costSignatureVariable := by
  change Option.map (mapTypeExpr source.costClosureSymbols)
      (source.costWholeRedexFreeContext source.costSignatureVariable) =
    Option.map
      (fun type =>
        if source.costSignatureVariable =
              source.costInteractionCut.program.continuationVariable.name ∨
            source.costSignatureVariable =
              source.costInteractionCut.environment.continuationVariable.name
        then costWrappedTypeExpr costWrappedSortName type
        else costBaseTypeExpr type)
      (source.costWholeRedexFreeContext source.costSignatureVariable)
  rw [source.costWholeRedexFreeContext_signature,
    source.costInteractionCut_program_continuationVariable_name,
    source.costInteractionCut_environment_continuationVariable_name]
  have notProgram :
      source.costSignatureVariable ≠
        costSourceSchemaName
          source.cut.program.continuationVariable.name :=
    (source.costSourceSchemaName_ne_signature
      source.cut.program.continuationVariable.name).symm
  have notEnvironment :
      source.costSignatureVariable ≠
        costSourceSchemaName
          source.cut.environment.continuationVariable.name :=
    (source.costSourceSchemaName_ne_signature
      source.cut.environment.continuationVariable.name).symm
  have notWrapped : costSignatureSortName ≠ costWrappedSortName :=
    (costWrappedSortName_ne_apparatus "signature").symm
  simp [notProgram, notEnvironment,
    source.mapTypeExpr_costClosureSymbols,
    costWrappedTypeExpr, costBaseTypeExpr, notWrapped]

/-- The generated token-stack tail is likewise base-tagged again and never
mistaken for a selected continuation. -/
theorem costClosureMappedFreeContext_stackTail (source : CIGSLT) :
    (source.costWholeRedexFreeContext.map source.costClosureSymbols)
        source.costStackTailVariable =
      source.costContinuationRetyping.generatedFreeContext
        source.costStackTailVariable := by
  change Option.map (mapTypeExpr source.costClosureSymbols)
      (source.costWholeRedexFreeContext source.costStackTailVariable) =
    Option.map
      (fun type =>
        if source.costStackTailVariable =
              source.costInteractionCut.program.continuationVariable.name ∨
            source.costStackTailVariable =
              source.costInteractionCut.environment.continuationVariable.name
        then costWrappedTypeExpr costWrappedSortName type
        else costBaseTypeExpr type)
      (source.costWholeRedexFreeContext source.costStackTailVariable)
  rw [source.costWholeRedexFreeContext_stackTail,
    source.costInteractionCut_program_continuationVariable_name,
    source.costInteractionCut_environment_continuationVariable_name]
  have notProgram :
      source.costStackTailVariable ≠
        costSourceSchemaName
          source.cut.program.continuationVariable.name :=
    (source.costSourceSchemaName_ne_stackTail
      source.cut.program.continuationVariable.name).symm
  have notEnvironment :
      source.costStackTailVariable ≠
        costSourceSchemaName
          source.cut.environment.continuationVariable.name :=
    (source.costSourceSchemaName_ne_stackTail
      source.cut.environment.continuationVariable.name).symm
  have notWrapped : costTokenStackSortName ≠ costWrappedSortName :=
    (costWrappedSortName_ne_apparatus "token-stack").symm
  simp [notProgram, notEnvironment,
    source.mapTypeExpr_costClosureSymbols,
    costWrappedTypeExpr, costBaseTypeExpr, notWrapped]

/-- Parameter-profile mapping and pattern mapping may use different sort and
constructor actions without changing whether an argument has the required
binder representation.  Representation matching observes only the
`TermParam` and `Pattern` constructors, not their type payloads. -/
theorem matchesParameterRepresentation_mixed_map_iff
    (parameterSymbols patternSymbols : PresentationSymbols)
    (parameter : TermParam) (pattern : Pattern) :
    MatchesParameterRepresentation (mapTermParam parameterSymbols parameter)
        (mapPattern patternSymbols pattern) ↔
      MatchesParameterRepresentation parameter pattern := by
  cases parameter <;> cases pattern <;>
    simp only [MatchesParameterRepresentation, mapTermParam, mapPattern]
  case abstractionNamed.lambda _ _ _ binder _ =>
    cases binder <;> simp
  case multiAbstractionNamed.multiLambda _ _ _ _ binders _ =>
    cases binders <;> simp

mutual
  /-- A term already lying in the generated base image admits the
  position-sensitive transport required by a second Cost layer.  Syntax
  receives another uniform base tag, while types follow `costClosureSymbols`
  so the distinguished wrapped continuation carrier remains wrapped.

  This is intentionally weaker than a `TypingMorphism` on the whole Cost
  language: wrapped-image constructors and administrative constructors do
  not satisfy the same constructor action. -/
  theorem mapCostBaseImageClosure
      (source : CIGSLT)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed :
        HasType source.continuationRetyping.generatedLanguage free bound
          (mapPattern costBasePresentationSymbols pattern) type) :
      HasType source.costContinuationRetyping.generatedLanguage
        (free.map source.costClosureSymbols)
        (bound.map (mapTypeExpr source.costClosureSymbols))
        (mapPattern costBasePresentationSymbols
          (mapPattern costBasePresentationSymbols pattern))
        (mapTypeExpr source.costClosureSymbols type) := by
    induction pattern using Pattern.inductionOn generalizing free bound type with
    | hbvar index =>
        cases typed with
        | bvar lookup =>
            have mappedLookup :
                (bound.map
                  (mapTypeExpr source.costClosureSymbols))[index]? =
                  some (mapTypeExpr source.costClosureSymbols type) := by
              simpa using congrArg
                (Option.map (mapTypeExpr source.costClosureSymbols)) lookup
            simpa [mapPattern] using
              (HasType.bvar
                (free := free.map source.costClosureSymbols) mappedLookup)
    | hfvar name =>
        cases typed with
        | fvar lookup =>
            have mappedLookup :
                (free.map source.costClosureSymbols) name =
                  some (mapTypeExpr source.costClosureSymbols type) := by
              simp [FreeTypeContext.map, lookup]
            simpa [mapPattern] using
              (HasType.fvar
                (bound :=
                  bound.map (mapTypeExpr source.costClosureSymbols))
                mappedLookup)
    | happly constructor arguments inductionHypothesis =>
        generalize patternEquality :
            mapPattern costBasePresentationSymbols
              (.apply constructor arguments) = mappedPattern at typed
        cases typed <;> simp [mapPattern] at patternEquality
        case constructor rule arguments' membership notBare argumentsTyped =>
            rcases patternEquality with
              ⟨mappedLabelEquality, argumentsEquality⟩
            subst arguments'
            have sourceArgumentsTyped :
                ArgumentsHaveTypes
                  source.continuationRetyping.generatedLanguage
                  free bound
                  (arguments.map
                    (mapPattern costBasePresentationSymbols))
                  rule.params :=
              argumentsTyped
            simp only [ContinuationRetypingPlan.generatedLanguage,
              List.mem_append, List.mem_map] at membership
            rcases membership with
              ⟨sourceRule, sourceMembership, ruleEquality⟩ |
              ⟨wrappedRule, _wrappedMembership, ruleEquality⟩
            · subst rule
              have sourceLabelEquality :
                  sourceRule.label = constructor := by
                apply costBaseConstructorName_injective
                simpa [costBasePresentationSymbols] using
                  mappedLabelEquality.symm
              subst constructor
              have targetArguments :=
                mapCostBaseImageClosureArguments source
                  sourceArgumentsTyped inductionHypothesis
              have targetNotBare :
                  ¬ UsesBareCollection
                    (costBaseConstructor source.costInteractionCut
                      (costBaseConstructor source.cut sourceRule)) := by
                intro targetBare
                exact notBare
                  ((usesBareCollection_costBaseConstructor_iff
                    source.costInteractionCut
                    (costBaseConstructor source.cut sourceRule)).mp
                      targetBare)
              have target :=
                HasType.constructor
                  (source.costContinuationRetyping.costBaseConstructor_mem_generated
                    (costBaseConstructor source.cut sourceRule)
                    (by
                      change costBaseConstructor source.cut sourceRule ∈
                        source.costWholeLanguage.terms
                      rw [source.costWholeLanguage_terms]
                      exact List.mem_append_left _
                        (source.continuationRetyping.costBaseConstructor_mem_generated
                          sourceRule sourceMembership)))
                  targetNotBare
                  (by
                    rw [← source.map_costClosure_costBaseConstructor_params
                      sourceRule sourceMembership]
                    exact targetArguments)
              simpa only [mapPattern, mapPatternList_eq_map, List.map_map,
                Function.comp_def, costBaseConstructor,
                costBasePresentationSymbols, mapTypeExpr,
                costClosureSymbols, costClosureSortName,
                costBaseSortName_ne_wrapped, if_false] using target
            · have generatedLabelEquality :=
                congrArg GrammarRule.label ruleEquality
              exact False.elim
                (costBaseConstructorName_ne_wrapped
                  constructor wrappedRule.1.label
                  (mappedLabelEquality.trans generatedLabelEquality.symm))
    | hlambda binder body inductionHypothesis =>
        cases typed with
        | lambda bodyTyped =>
            simpa [mapPattern, mapTypeExpr] using
              (HasType.lambda
                (inductionHypothesis bodyTyped))
    | hmultiLambda arity binders body inductionHypothesis =>
        cases typed with
        | multiLambda bodyTyped =>
            have mappedBody := inductionHypothesis bodyTyped
            rw [List.map_append, List.map_replicate] at mappedBody
            simpa only [mapPattern, mapTypeExpr] using
              (HasType.multiLambda mappedBody)
    | hsubst body replacement bodyInduction replacementInduction =>
        cases typed with
        | subst bodyTyped replacementTyped =>
            simpa [mapPattern] using
              (HasType.subst
                (bodyInduction bodyTyped)
                (replacementInduction replacementTyped))
    | hcollection collectionType elements rest inductionHypothesis =>
        cases typed with
        | @collection _ _ _ _ elementType elementsTyped =>
            have sourceElementsTyped :
                ElementsHaveType
                  source.continuationRetyping.generatedLanguage
                  free bound
                  (elements.map
                    (mapPattern costBasePresentationSymbols))
                  elementType := by
              simpa [mapPatternList_eq_map] using elementsTyped
            have targetElements :=
              mapCostBaseImageClosureElements source
                sourceElementsTyped inductionHypothesis
            simpa only [mapPattern, mapPatternList_eq_map, List.map_map,
              Function.comp_def, mapTypeExpr] using
                (HasType.collection (rest := rest) targetElements)
        | @collectionConstructor _ rule parameterName _ _ _ elementType
            membership parameterShape elementsTyped =>
            have sourceElementsTyped :
                ElementsHaveType
                  source.continuationRetyping.generatedLanguage
                  free bound
                  (elements.map
                    (mapPattern costBasePresentationSymbols))
                  elementType := by
              simpa [mapPatternList_eq_map] using elementsTyped
            have targetElements :=
              mapCostBaseImageClosureElements source
                sourceElementsTyped inductionHypothesis
            have wholeMembership :
                rule ∈ source.costWholePresentation.language.terms := by
              change rule ∈ source.costWholeLanguage.terms
              rw [source.costWholeLanguage_terms]
              exact List.mem_append_left _ membership
            obtain ⟨targetRule, targetMembership, _targetLabel,
                targetCategory, targetParameters⟩ :=
              source.costClosureTyping.mapsTerms rule wholeMembership
            have targetShape :
                targetRule.params =
                  [.simple parameterName
                    (.collection collectionType
                      (mapTypeExpr source.costClosureSymbols
                        elementType))] := by
              rw [targetParameters, parameterShape]
              rfl
            have targetCategory' :
                targetRule.category =
                  source.costClosureSortName rule.category := by
              simpa [costClosureTyping, costClosureSymbols] using
                targetCategory
            have target :=
              HasType.collectionConstructor
                (rest := rest) targetMembership targetShape targetElements
            simpa only [mapPattern, mapPatternList_eq_map, List.map_map,
              Function.comp_def, mapTypeExpr, costClosureSymbols,
              ContinuationRetypingPlan.generatedPresentation,
              targetCategory'] using target

  /-- Ordered-argument companion to
  `HasType.mapCostBaseImageClosure`. -/
  theorem mapCostBaseImageClosureArguments
      (source : CIGSLT)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam}
      (typed :
        ArgumentsHaveTypes source.continuationRetyping.generatedLanguage
          free bound
          (patterns.map (mapPattern costBasePresentationSymbols))
          parameters)
      (inductionHypothesis : ∀ pattern ∈ patterns,
        ∀ {free : FreeTypeContext} {bound : List TypeExpr}
          {type : TypeExpr},
          HasType source.continuationRetyping.generatedLanguage
            free bound (mapPattern costBasePresentationSymbols pattern) type →
          HasType source.costContinuationRetyping.generatedLanguage
            (free.map source.costClosureSymbols)
            (bound.map (mapTypeExpr source.costClosureSymbols))
            (mapPattern costBasePresentationSymbols
              (mapPattern costBasePresentationSymbols pattern))
            (mapTypeExpr source.costClosureSymbols type)) :
      ArgumentsHaveTypes source.costContinuationRetyping.generatedLanguage
        (free.map source.costClosureSymbols)
        (bound.map (mapTypeExpr source.costClosureSymbols))
        (patterns.map fun pattern =>
          mapPattern costBasePresentationSymbols
            (mapPattern costBasePresentationSymbols pattern))
        (parameters.map (mapTermParam source.costClosureSymbols)) := by
    induction patterns generalizing parameters with
    | nil =>
        cases typed
        exact .nil
    | cons pattern patterns tailInduction =>
        cases typed with
        | @cons _ _ _ parameter _ expected representation parameterType
            headTyped tailTyped =>
            have mappedRepresentation :
                MatchesParameterRepresentation
                  (mapTermParam source.costClosureSymbols parameter)
                  (mapPattern costBasePresentationSymbols
                    (mapPattern costBasePresentationSymbols pattern)) :=
              (matchesParameterRepresentation_mixed_map_iff
                source.costClosureSymbols costBasePresentationSymbols
                parameter
                (mapPattern costBasePresentationSymbols pattern)).2
                  representation
            have mappedParameterType :
                parameterType?
                    (mapTermParam source.costClosureSymbols parameter) =
                  some (mapTypeExpr source.costClosureSymbols expected) := by
              rw [parameterType?_mapTermParam, parameterType]
              rfl
            exact .cons mappedRepresentation mappedParameterType
              (inductionHypothesis pattern (by simp) headTyped)
              (tailInduction tailTyped
                (fun nested membership =>
                  inductionHypothesis nested (by simp [membership])))

  /-- Homogeneous-collection companion to
  `HasType.mapCostBaseImageClosure`. -/
  theorem mapCostBaseImageClosureElements
      (source : CIGSLT)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {type : TypeExpr}
      (typed :
        ElementsHaveType source.continuationRetyping.generatedLanguage
          free bound
          (patterns.map (mapPattern costBasePresentationSymbols))
          type)
      (inductionHypothesis : ∀ pattern ∈ patterns,
        ∀ {free : FreeTypeContext} {bound : List TypeExpr}
          {type : TypeExpr},
          HasType source.continuationRetyping.generatedLanguage
            free bound (mapPattern costBasePresentationSymbols pattern) type →
          HasType source.costContinuationRetyping.generatedLanguage
            (free.map source.costClosureSymbols)
            (bound.map (mapTypeExpr source.costClosureSymbols))
            (mapPattern costBasePresentationSymbols
              (mapPattern costBasePresentationSymbols pattern))
            (mapTypeExpr source.costClosureSymbols type)) :
      ElementsHaveType source.costContinuationRetyping.generatedLanguage
        (free.map source.costClosureSymbols)
        (bound.map (mapTypeExpr source.costClosureSymbols))
        (patterns.map fun pattern =>
          mapPattern costBasePresentationSymbols
            (mapPattern costBasePresentationSymbols pattern))
        (mapTypeExpr source.costClosureSymbols type) := by
    induction patterns with
    | nil =>
        exact .nil _ _
    | cons pattern patterns tailInduction =>
        cases typed with
        | cons headTyped tailTyped =>
            exact .cons
              (inductionHypothesis pattern (by simp) headTyped)
              (tailInduction tailTyped
                (fun nested membership =>
                  inductionHypothesis nested (by simp [membership])))
end

/-- The exact generated Cost contractum remains in the wrapped carrier at the
next Cost layer.  The proof transports its current typing derivation and then
changes only the unused part of the free-variable context. -/
theorem costWrappable (source : CIGSLT) :
    source.costContinuationRetyping.Wrappable := by
  have current :
      HasSort source.costWholeLanguage source.costWholeRedexFreeContext []
        source.costWholeRedexTarget costWrappedSortName := by
    exact source.costWholeRedexTarget_hasType.weakenTerms
      (fun rule membership => by
        simpa only [source.costWholeLanguage_terms] using membership)
  have mapped := current.mapTyping source.costClosureTyping
  change HasType source.costContinuationRetyping.generatedLanguage
      (source.costWholeRedexFreeContext.map source.costClosureSymbols) []
      (mapPattern source.costClosureSymbols source.costWholeRedexTarget)
      (mapTypeExpr source.costClosureSymbols (.base costWrappedSortName))
    at mapped
  have mappedTyped :
      HasSort source.costContinuationRetyping.generatedLanguage
        (source.costWholeRedexFreeContext.map source.costClosureSymbols) []
        (source.costContinuationRetyping.mapContractum
          source.costWholeRedexTarget) costWrappedSortName := by
    rw [source.mapContractum_eq_mapPattern_of_hasType current]
    simpa [source.mapTypeExpr_costClosureSymbols,
      costWrappedTypeExpr] using mapped
  apply mappedTyped.recontextualizeFree
  intro name freeType membership lookup
  rw [source.costContinuationRetyping.mapContractum_freeFvarNames,
    source.costWholeRedexTarget_freeFvarNames] at membership
  rcases List.mem_append.mp membership with
      sourceMembership | tailMembership
  · rcases List.mem_map.mp sourceMembership with
      ⟨sourceName, _sourceMembership, rfl⟩
    rw [← source.costClosureMappedFreeContext_source sourceName]
    exact lookup
  · simp only [List.mem_singleton] at tailMembership
    subst name
    rw [← source.costClosureMappedFreeContext_stackTail]
    exact lookup

/-- The preceding interaction redex, after its first base translation, admits
the position-sensitive base-image transport needed by the next Cost layer.
Schema renaming then aligns the transported source variables with the next
generated free context. -/
theorem costBaseMappedRedex_retyped (source : CIGSLT) :
    HasSort source.costContinuationRetyping.generatedLanguage
      source.costContinuationRetyping.generatedFreeContext []
      (mapPattern costBasePresentationSymbols
        (mapPatternSchemaNames costSourceSchemaName
          (mapPattern costBasePresentationSymbols
            source.theory.presentation.interactionRewrite.1.left)))
      (costBaseSortName
        (costBaseSortName
          source.theory.presentation.interactingSort.1.name)) := by
  have mapped :=
    mapCostBaseImageClosure source source.redexRetypable
  have renamed := mapped.mapSchemaNames
      (targetFree :=
        source.costContinuationRetyping.generatedFreeContext)
      costSourceSchemaName (by
    intro name type lookup
    rw [← source.costClosureMappedFreeContext_source name]
    change Option.map (mapTypeExpr source.costClosureSymbols)
        (source.costWholeRedexFreeContext (costSourceSchemaName name)) =
      some type
    change Option.map (mapTypeExpr source.costClosureSymbols)
        (source.continuationRetyping.generatedFreeContext name) =
      some type at lookup
    generalize currentLookup :
        source.continuationRetyping.generatedFreeContext name = result
      at lookup
    cases result with
    | none => simp at lookup
    | some currentType =>
        rw [source.costWholeRedexFreeContext_source name currentType
          currentLookup]
        exact lookup)
  simpa only [mapPattern_mapPatternSchemaNames, List.map_nil,
    mapTypeExpr, costClosureSymbols, costClosureSortName,
    costBaseSortName_ne_wrapped, if_false] using renamed

private theorem costApparatusConstructor_not_selected
    (source : CIGSLT) (rule : GrammarRule) (suffix : String)
    (label : rule.label = costApparatusConstructorName suffix)
    (index : Nat) :
    isSelectedContinuation source.costInteractionCut rule index = false := by
  have notProgram :
      rule ≠ source.costInteractionCut.program.constructor.1 := by
    rw [source.costInteractionCut_program_constructor]
    intro equality
    have labelEquality := congrArg GrammarRule.label equality
    exact costBaseConstructorName_ne_apparatus
      source.cut.program.constructor.1.label suffix
      (labelEquality.symm.trans label)
  have notEnvironment :
      rule ≠ source.costInteractionCut.environment.constructor.1 := by
    rw [source.costInteractionCut_environment_constructor]
    intro equality
    have labelEquality := congrArg GrammarRule.label equality
    exact costBaseConstructorName_ne_apparatus
      source.cut.environment.constructor.1.label suffix
      (labelEquality.symm.trans label)
  apply Bool.eq_false_iff.mpr
  intro selected
  simp only [isSelectedContinuation, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at selected
  rcases selected with selected | selected
  · exact notProgram selected.1
  · exact notEnvironment selected.1

private theorem costBaseConstructor_params_eq_map_of_notSelected
    (cut : InteractionCutPresentation source)
    (rule : GrammarRule)
    (notSelected : ∀ index,
      isSelectedContinuation cut rule index = false) :
    (costBaseConstructor cut rule).params =
      rule.params.map (mapParameterType costBaseTypeExpr) := by
  apply List.ext_getElem
  · rw [List.length_map, costBaseConstructor_params_length]
  · intro index leftBounds rightBounds
    have sourceBounds : index < rule.params.length := by
      simpa using rightBounds
    rw [costBaseConstructor_parameter cut rule index sourceBounds,
      List.getElem_map]
    unfold costBaseParameter
    rw [notSelected index]
    simp

/-- The next Cost layer's signature variable has the twice-generated
signature sort. -/
theorem costClosureSignatureVariable_hasType (source : CIGSLT) :
    HasSort source.costContinuationRetyping.generatedLanguage
      source.costContinuationRetyping.generatedFreeContext []
      (.fvar source.costSignatureVariable)
      (costBaseSortName costSignatureSortName) := by
  apply HasType.fvar
  rw [← source.costClosureMappedFreeContext_signature]
  change Option.map (mapTypeExpr source.costClosureSymbols)
      (source.costWholeRedexFreeContext source.costSignatureVariable) =
    some (.base (costBaseSortName costSignatureSortName))
  rw [source.costWholeRedexFreeContext_signature]
  have notWrapped : costSignatureSortName ≠ costWrappedSortName :=
    (costWrappedSortName_ne_apparatus "signature").symm
  simp [source.mapTypeExpr_costClosureSymbols, costWrappedTypeExpr,
    notWrapped]

/-- The next Cost layer's residual token-stack variable has the
twice-generated token-stack sort. -/
theorem costClosureStackTailVariable_hasType (source : CIGSLT) :
    HasSort source.costContinuationRetyping.generatedLanguage
      source.costContinuationRetyping.generatedFreeContext []
      (.fvar source.costStackTailVariable)
      (costBaseSortName costTokenStackSortName) := by
  apply HasType.fvar
  rw [← source.costClosureMappedFreeContext_stackTail]
  change Option.map (mapTypeExpr source.costClosureSymbols)
      (source.costWholeRedexFreeContext source.costStackTailVariable) =
    some (.base (costBaseSortName costTokenStackSortName))
  rw [source.costWholeRedexFreeContext_stackTail]
  have notWrapped : costTokenStackSortName ≠ costWrappedSortName :=
    (costWrappedSortName_ne_apparatus "token-stack").symm
  simp [source.mapTypeExpr_costClosureSymbols, costWrappedTypeExpr,
    notWrapped]

private theorem costBaseApparatusConstructor_mem_generated
    (source : CIGSLT) (rule : GrammarRule)
    (membership : rule ∈
      costCoreConstructors
        source.theory.presentation.interactingSort.1.name) :
    costBaseConstructor source.costInteractionCut rule ∈
      source.costContinuationRetyping.generatedLanguage.terms := by
  apply source.costContinuationRetyping.costBaseConstructor_mem_generated
  change rule ∈ source.costWholeLanguage.terms
  rw [source.costWholeLanguage_terms]
  exact List.mem_append_right _ membership

/-- The next Cost layer types the signed redex operand once its transported
body has the twice-generated interacting sort. -/
theorem costClosureSigned_hasType (source : CIGSLT) {body : Pattern}
    (bodyTyped :
      HasSort source.costContinuationRetyping.generatedLanguage
        source.costContinuationRetyping.generatedFreeContext []
        body
        (costBaseSortName
          (costBaseSortName
            source.theory.presentation.interactingSort.1.name))) :
    HasSort source.costContinuationRetyping.generatedLanguage
      source.costContinuationRetyping.generatedFreeContext []
      (.apply (costBaseConstructorName costSignedConstructorName)
        [body, .fvar source.costSignatureVariable])
      (costBaseSortName costWrappedSortName) := by
  let rule :=
    costSignedConstructor
      source.theory.presentation.interactingSort.1.name
  have parameters :
      (costBaseConstructor source.costInteractionCut rule).params =
        [.simple "body"
            (.base
              (costBaseSortName
                (costBaseSortName
                  source.theory.presentation.interactingSort.1.name))),
          .simple "signature"
            (.base (costBaseSortName costSignatureSortName))] := by
    rw [costBaseConstructor_params_eq_map_of_notSelected
      source.costInteractionCut rule
      (costApparatusConstructor_not_selected source rule "signed" rfl)]
    simp [rule, costSignedConstructor, mapParameterType,
      costBaseTypeExpr]
  have target :=
    HasType.constructor
      (costBaseApparatusConstructor_mem_generated source rule
        (by simp [rule, costCoreConstructors]))
      (by
        intro bare
        simpa [rule, UsesBareCollection, costSignedConstructor] using
          ((usesBareCollection_costBaseConstructor_iff
            source.costInteractionCut rule).mp bare))
      (by
        rw [parameters]
        exact .cons trivial rfl bodyTyped
          (.cons trivial rfl
            (costClosureSignatureVariable_hasType source) .nil))
  simpa [rule, costBaseConstructor, costSignedConstructor] using target

/-- The next Cost layer types the apparatus cell that restores the consumed
signature to the residual token stack. -/
theorem costClosureTokenStackCons_hasType (source : CIGSLT) :
    HasSort source.costContinuationRetyping.generatedLanguage
      source.costContinuationRetyping.generatedFreeContext []
      (.apply (costBaseConstructorName costTokenStackConsConstructorName)
        [.fvar source.costSignatureVariable,
          .fvar source.costStackTailVariable])
      (costBaseSortName costTokenStackSortName) := by
  let rule := costTokenStackConsConstructor
  have parameters :
      (costBaseConstructor source.costInteractionCut rule).params =
        [.simple "head" (.base (costBaseSortName costSignatureSortName)),
          .simple "tail"
            (.base (costBaseSortName costTokenStackSortName))] := by
    rw [costBaseConstructor_params_eq_map_of_notSelected
      source.costInteractionCut rule
      (costApparatusConstructor_not_selected source rule
        "token-stack-cons" rfl)]
    simp [rule, costTokenStackConsConstructor, mapParameterType,
      costBaseTypeExpr]
  have target :=
    HasType.constructor
      (costBaseApparatusConstructor_mem_generated source rule
        (by simp [rule, costCoreConstructors]))
      (by
        intro bare
        simpa [rule, UsesBareCollection,
          costTokenStackConsConstructor] using
            ((usesBareCollection_costBaseConstructor_iff
              source.costInteractionCut rule).mp bare))
      (by
        rw [parameters]
        exact .cons trivial rfl
          (costClosureSignatureVariable_hasType source)
          (.cons trivial rfl
            (costClosureStackTailVariable_hasType source) .nil))
  simpa [rule, costBaseConstructor, costTokenStackConsConstructor] using
    target

/-- The next Cost layer types a funding apparatus around a typed token
stack. -/
theorem costClosureFunding_hasType (source : CIGSLT) {stack : Pattern}
    (stackTyped :
      HasSort source.costContinuationRetyping.generatedLanguage
        source.costContinuationRetyping.generatedFreeContext []
        stack (costBaseSortName costTokenStackSortName)) :
    HasSort source.costContinuationRetyping.generatedLanguage
      source.costContinuationRetyping.generatedFreeContext []
      (.apply (costBaseConstructorName costFundingConstructorName) [stack])
      (costBaseSortName costWrappedSortName) := by
  let rule := costFundingConstructor
  have parameters :
      (costBaseConstructor source.costInteractionCut rule).params =
        [.simple "stack"
          (.base (costBaseSortName costTokenStackSortName))] := by
    rw [costBaseConstructor_params_eq_map_of_notSelected
      source.costInteractionCut rule
      (costApparatusConstructor_not_selected source rule "funding" rfl)]
    simp [rule, costFundingConstructor, mapParameterType,
      costBaseTypeExpr]
  have target :=
    HasType.constructor
      (costBaseApparatusConstructor_mem_generated source rule
        (by simp [rule, costCoreConstructors]))
      (by
        intro bare
        simpa [rule, UsesBareCollection, costFundingConstructor] using
          ((usesBareCollection_costBaseConstructor_iff
            source.costInteractionCut rule).mp bare))
      (by
        rw [parameters]
        exact .cons trivial rfl stackTyped .nil)
  simpa [rule, costBaseConstructor, costFundingConstructor] using target

/-- The next Cost layer types the outer contact apparatus from two wrapped
operands. -/
theorem costClosureContact_hasType (source : CIGSLT)
    {left right : Pattern}
    (leftTyped :
      HasSort source.costContinuationRetyping.generatedLanguage
        source.costContinuationRetyping.generatedFreeContext []
        left (costBaseSortName costWrappedSortName))
    (rightTyped :
      HasSort source.costContinuationRetyping.generatedLanguage
        source.costContinuationRetyping.generatedFreeContext []
        right (costBaseSortName costWrappedSortName)) :
    HasSort source.costContinuationRetyping.generatedLanguage
      source.costContinuationRetyping.generatedFreeContext []
      (.apply (costBaseConstructorName costContactConstructorName)
        [left, right])
      (costBaseSortName costWrappedSortName) := by
  let rule := costContactConstructor
  have parameters :
      (costBaseConstructor source.costInteractionCut rule).params =
        [.simple "left"
            (.base (costBaseSortName costWrappedSortName)),
          .simple "right"
            (.base (costBaseSortName costWrappedSortName))] := by
    rw [costBaseConstructor_params_eq_map_of_notSelected
      source.costInteractionCut rule
      (costApparatusConstructor_not_selected source rule "contact" rfl)]
    simp [rule, costContactConstructor, mapParameterType,
      costBaseTypeExpr]
  have target :=
    HasType.constructor
      (costBaseApparatusConstructor_mem_generated source rule
        (by simp [rule, costCoreConstructors]))
      (by
        intro bare
        simpa [rule, UsesBareCollection, costContactConstructor] using
          ((usesBareCollection_costBaseConstructor_iff
            source.costInteractionCut rule).mp bare))
      (by
        rw [parameters]
        exact .cons trivial rfl leftTyped
          (.cons trivial rfl rightTyped .nil))
  simpa [rule, costBaseConstructor, costContactConstructor] using target

/-- The generated Cost redex is well-sorted after a second Cost
transformation.  Its prior interaction core uses the restricted base-image
transport, while the fixed outer Cost apparatus is typed constructor by
constructor. -/
theorem costRedexRetypable (source : CIGSLT) :
    source.costContinuationRetyping.RedexRetypable := by
  unfold ContinuationRetypingPlan.RedexRetypable
  change
    HasSort source.costContinuationRetyping.generatedLanguage
      source.costContinuationRetyping.generatedFreeContext []
      (mapPattern costBasePresentationSymbols source.costWholeRedexSource)
      (costBaseSortName costWrappedSortName)
  rw [source.costWholeRedexSource_eq]
  simpa [mapPattern, mapPatternList_eq_map,
    costBasePresentationSymbols] using
    costClosureContact_hasType source
      (costClosureSigned_hasType source
        (costBaseMappedRedex_retyped source))
      (costClosureFunding_hasType source
        (costClosureTokenStackCons_hasType source))

/-- The selected program introduction cannot use a bare collection: the
continued-object law would place it in the wrapped fragment, while the cut
definition excludes that principal constructor. -/
theorem programConstructor_not_usesBareCollection (source : CIGSLT) :
    ¬ WellSorted.UsesBareCollection source.cut.program.constructor.1 := by
  intro bare
  have labelMembership :=
    source.bareCollectionConstructorsWrapped
      source.cut.program.constructor.1
      source.cut.program.constructor.2 bare
  have constructorMembership :=
    (source.continuationRetyping.mem_wrappedLabels_iff
      source.cut.program.constructor).1 labelMembership
  exact source.continuationRetyping.programNotWrapped constructorMembership

/-- The selected environment introduction is likewise never a bare
collection constructor. -/
theorem environmentConstructor_not_usesBareCollection (source : CIGSLT) :
    ¬ WellSorted.UsesBareCollection
      source.cut.environment.constructor.1 := by
  intro bare
  have labelMembership :=
    source.bareCollectionConstructorsWrapped
      source.cut.environment.constructor.1
      source.cut.environment.constructor.2 bare
  have constructorMembership :=
    (source.continuationRetyping.mem_wrappedLabels_iff
      source.cut.environment.constructor).1 labelMembership
  exact source.continuationRetyping.environmentNotWrapped
    constructorMembership

/-- Every bare collection constructor of the generated Cost language belongs
to the hereditary non-principal fragment of the next Cost layer. -/
theorem costBareCollectionConstructorsWrapped (source : CIGSLT) :
    ∀ rule ∈ source.costWholeLanguage.terms,
      WellSorted.UsesBareCollection rule →
        rule.label ∈ source.costContinuationRetyping.wrappedLabels := by
  intro rule membership bare
  let constructor :
      AuthoredConstructor source.costIGSLT.presentation.presentation :=
    ⟨rule, membership⟩
  apply (source.costContinuationRetyping.mem_wrappedLabels_iff
    constructor).2
  rw [source.costContinuationRetyping.mem_wrappedConstructors_iff]
  constructor
  · intro equality
    have rawEquality := congrArg Subtype.val equality
    have programBare :
        WellSorted.UsesBareCollection
          source.costInteractionCut.program.constructor.1 := by
      rw [← rawEquality]
      exact bare
    rw [source.costInteractionCut_program_constructor] at programBare
    exact source.programConstructor_not_usesBareCollection
      ((usesBareCollection_costBaseConstructor_iff
        source.cut source.cut.program.constructor.1).1 programBare)
  · intro equality
    have rawEquality := congrArg Subtype.val equality
    have environmentBare :
        WellSorted.UsesBareCollection
          source.costInteractionCut.environment.constructor.1 := by
      rw [← rawEquality]
      exact bare
    rw [source.costInteractionCut_environment_constructor] at environmentBare
    exact source.environmentConstructor_not_usesBareCollection
      ((usesBareCollection_costBaseConstructor_iff
        source.cut source.cut.environment.constructor.1).1 environmentBare)

/-- The complete generated interaction envelope remains outside the retained
continuation slots, exactly as required by the next continued object. -/
theorem costSourceEnvelopeStable (source : CIGSLT) :
    ContinuationStableContext source.costInteractionCut
      source.costInteractionCut.coreContact.sort.1.name
      source.costIGSLT.presentation.interactingSort.1.name
      source.costInteractionCut.sourceShape.envelope := by
  simpa [costInteractionCut, costWholeCutSource, costIGSLT,
    costWholeInteractivePresentation, costWholeInteractingSort,
    costBaseCoreContact, TypeDecl.plain,
    costBaseAuthoredSort] using source.costWholeRedexEnvelopeStable

/-- Raw declaration membership plus exclusion of the two retained
introductions is exactly enough to enter the next hereditary continuation
fragment. -/
theorem costContinuationLabel_mem_of_ne_principals (source : CIGSLT)
    (rule : GrammarRule) (membership : rule ∈ source.costWholeLanguage.terms)
    (notProgram :
      rule ≠ source.costInteractionCut.program.constructor.1)
    (notEnvironment :
      rule ≠ source.costInteractionCut.environment.constructor.1) :
    rule.label ∈ source.costContinuationRetyping.wrappedLabels := by
  let authored :
      AuthoredConstructor source.costIGSLT.presentation.presentation :=
    ⟨rule, membership⟩
  apply (source.costContinuationRetyping.mem_wrappedLabels_iff authored).2
  apply (source.costContinuationRetyping.mem_wrappedConstructors_iff
    authored).2
  constructor
  · intro equality
    exact notProgram (congrArg Subtype.val equality)
  · intro equality
    exact notEnvironment (congrArg Subtype.val equality)

/-- Either static image of an authored non-principal constructor remains
non-principal at the next Cost layer. -/
theorem costStaticConstructorLabel_mem_costContinuationLabels
    (source : CIGSLT) (color : CostStaticColor)
    (rule : GrammarRule)
    (membership :
      rule ∈ source.theory.presentation.presentation.language.terms)
    (wrapped :
      rule.label ∈ source.continuationRetyping.wrappedLabels) :
    (color.symbols source).constructor rule.label ∈
      source.costContinuationRetyping.wrappedLabels := by
  let authored :
      AuthoredConstructor source.theory.presentation.presentation :=
    ⟨rule, membership⟩
  have sourceNonprincipal :=
    (source.continuationRetyping.mem_wrappedConstructors_iff authored).1
      ((source.continuationRetyping.mem_wrappedLabels_iff authored).1 wrapped)
  cases color with
  | base =>
      apply source.costContinuationLabel_mem_of_ne_principals
        (costBaseConstructor source.cut rule)
        (source.costBaseConstructor_mem_costWhole rule membership)
      · intro equality
        exact sourceNonprincipal.1 (Subtype.ext
          ((source.costBaseConstructor_eq_program_iff rule membership).1
            equality))
      · intro equality
        exact sourceNonprincipal.2 (Subtype.ext
          ((source.costBaseConstructor_eq_environment_iff rule membership).1
            equality))
  | wrapped =>
      have wrappedMembership : authored ∈
          source.continuationRetyping.wrappedConstructors :=
        (source.continuationRetyping.mem_wrappedLabels_iff authored).1 wrapped
      apply source.costContinuationLabel_mem_of_ne_principals
        (costWrappedConstructor (theory := source.theory) rule)
        (source.costWrappedConstructor_mem_costWhole authored
          wrappedMembership)
      · intro equality
        rw [source.costInteractionCut_program_constructor] at equality
        have labelEquality := congrArg GrammarRule.label equality
        exact costBaseConstructorName_ne_wrapped
          source.cut.program.constructor.1.label rule.label labelEquality.symm
      · intro equality
        rw [source.costInteractionCut_environment_constructor] at equality
        have labelEquality := congrArg GrammarRule.label equality
        exact costBaseConstructorName_ne_wrapped
          source.cut.environment.constructor.1.label rule.label
            labelEquality.symm

/-- Membership in the source wrapped-label fiber is sufficient to transport
one visible constructor label into either static fiber of the next Cost
layer.  Validation makes the label projection faithful, so no declaration
identity is guessed here. -/
theorem costStaticConstructorLabel_mem_costContinuationLabels_of_mem
    (source : CIGSLT) (color : CostStaticColor) (constructor : String)
    (wrapped :
      constructor ∈ source.continuationRetyping.wrappedLabels) :
    (color.symbols source).constructor constructor ∈
      source.costContinuationRetyping.wrappedLabels := by
  rcases List.mem_map.mp wrapped with
    ⟨authored, authoredMembership, labelEquality⟩
  rw [← labelEquality]
  exact source.costStaticConstructorLabel_mem_costContinuationLabels
    color authored.1 authored.2
      (List.mem_map.mpr ⟨authored, authoredMembership, rfl⟩)

/-- Every constructor named by a generated static reflective presentation
remains in the hereditary continuation fragment of the next Cost layer.
The proof transports the source declaration's validated wrapped support
through the same static color that produced the generated declaration. -/
theorem costStaticReflectivePresentation_constructorLabels_mem
    (source : CIGSLT) (declaration : ReflectivePresentationDecl)
    (membership :
      declaration ∈ source.costStaticReflectivePresentations) :
    declaration.quoteConstructor ∈
        source.costContinuationRetyping.wrappedLabels ∧
      declaration.dropConstructor ∈
        source.costContinuationRetyping.wrappedLabels ∧
      declaration.parallelUnitConstructor ∈
        source.costContinuationRetyping.wrappedLabels := by
  rw [costStaticReflectivePresentations, List.mem_append] at membership
  rcases membership with baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨sourceDeclaration, sourceMembership, rfl⟩
    have sourceLabels :=
      (source.reflectivePresentationsRetypable sourceDeclaration
        sourceMembership).constructorLabels_mem_wrapped
    exact ⟨
      source.costStaticConstructorLabel_mem_costContinuationLabels_of_mem
        .base sourceDeclaration.quoteConstructor sourceLabels.1,
      source.costStaticConstructorLabel_mem_costContinuationLabels_of_mem
        .base sourceDeclaration.dropConstructor sourceLabels.2.1,
      source.costStaticConstructorLabel_mem_costContinuationLabels_of_mem
        .base sourceDeclaration.parallelUnitConstructor sourceLabels.2.2⟩
  · rcases List.mem_map.mp wrappedMembership with
      ⟨sourceDeclaration, sourceMembership, rfl⟩
    have sourceLabels :=
      (source.reflectivePresentationsRetypable sourceDeclaration
        sourceMembership).constructorLabels_mem_wrapped
    exact ⟨
      source.costStaticConstructorLabel_mem_costContinuationLabels_of_mem
        .wrapped sourceDeclaration.quoteConstructor sourceLabels.1,
      source.costStaticConstructorLabel_mem_costContinuationLabels_of_mem
        .wrapped sourceDeclaration.dropConstructor sourceLabels.2.1,
      source.costStaticConstructorLabel_mem_costContinuationLabels_of_mem
        .wrapped sourceDeclaration.parallelUnitConstructor
          sourceLabels.2.2⟩

/-- The complete generated reflective theory satisfies the same exact
validator-based hereditary retyping obligation required by another Cost
layer. -/
theorem costReflectivePresentationsRetypable (source : CIGSLT) :
    ReflectivePresentationsRetypable source.costContinuationRetyping
      source.costWholeReflectionProfile := by
  intro declaration membership
  change declaration ∈ source.costStaticReflectivePresentations at membership
  have labels :=
    source.costStaticReflectivePresentation_constructorLabels_mem
      declaration membership
  exact reflectivePresentationRetypable_of_validate_of_wrapped
    source.costContinuationRetyping declaration
      (source.costStaticReflectivePresentation_validate declaration membership)
      labels.1 labels.2.1 labels.2.2

/-- Static symbol transport followed by schema-local alpha-renaming maps
visible constructor support into the hereditary fragment of the next Cost
layer. -/
theorem costStaticSchemaPattern_constructorsWithin
    (source : CIGSLT) (color : CostStaticColor) {pattern : Pattern}
    (supported :
      ConstructorsWithin
        (· ∈ source.continuationRetyping.wrappedLabels) pattern) :
    ConstructorsWithin
      (· ∈ source.costContinuationRetyping.wrappedLabels)
      (mapPatternSchemaNames costSourceSchemaName
        (mapPattern (color.symbols source) pattern)) := by
  apply constructorsWithin_mapPatternSchemaNames
  apply constructorsWithin_mapPattern (color.symbols source)
  · intro constructor membership
    exact
      source.costStaticConstructorLabel_mem_costContinuationLabels_of_mem
        color constructor membership
  · exact supported

/-- Each finalized static equation declaration admits proof-relevant
constructor typing in the complete Cost language.  Visible constructor
support is recovered from the already-certified wrapped source image;
hidden bare-collection choices are covered by the continued-object law. -/
theorem costStaticEquationDecl_wellSortedWithConstructors
    (source : CIGSLT) (color : CostStaticColor) (equation : Equation)
    (membership : equation ∈
      source.theory.presentation.presentation.language.equations) :
    ∃ type,
      WellSorted.HasTypeWithConstructors source.costWholeLanguage
          (· ∈ source.costContinuationRetyping.wrappedLabels)
          (WellSorted.FreeTypeContext.ofList
            (costStaticEquationDecl source color equation).typeContext)
          [] (costStaticEquationDecl source color equation).left type ∧
        WellSorted.HasTypeWithConstructors source.costWholeLanguage
          (· ∈ source.costContinuationRetyping.wrappedLabels)
          (WellSorted.FreeTypeContext.ofList
            (costStaticEquationDecl source color equation).typeContext)
          [] (costStaticEquationDecl source color equation).right type := by
  rcases
      (source.equationsRetypable equation membership).wrappedWellSorted with
    ⟨_wrappedType, sourceLeftWrapped, sourceRightWrapped⟩
  have sourceLeftSupported :
      ConstructorsWithin
        (· ∈ source.continuationRetyping.wrappedLabels) equation.left :=
    sourceLeftWrapped.sourceConstructorsWithin_of_wrappedImage
      source.continuationRetyping
  have sourceRightSupported :
      ConstructorsWithin
        (· ∈ source.continuationRetyping.wrappedLabels) equation.right :=
    sourceRightWrapped.sourceConstructorsWithin_of_wrappedImage
      source.continuationRetyping
  have leftSupported :=
    source.costStaticSchemaPattern_constructorsWithin color
      sourceLeftSupported
  have rightSupported :=
    source.costStaticSchemaPattern_constructorsWithin color
      sourceRightSupported
  have plain :
      EquationWellSorted source.costWholeLanguage
        (costStaticEquationDecl source color equation) := by
    cases color with
    | base =>
        exact source.costBaseEquationDecl_wellSorted equation membership
    | wrapped =>
        exact source.costWrappedEquationDecl_wellSorted equation membership
  rcases plain with ⟨type, leftTyped, rightTyped⟩
  refine ⟨type, leftTyped.withConstructors ?_
    source.costBareCollectionConstructorsWrapped,
    rightTyped.withConstructors ?_
      source.costBareCollectionConstructorsWrapped⟩
  · simpa only [costStaticEquationDecl_left,
      mapCostStaticSchemaPattern] using leftSupported
  · simpa only [costStaticEquationDecl_right,
      mapCostStaticSchemaPattern] using rightSupported

/-- Either next-layer static image of a finalized source-layer equation is
well sorted in the bare generated continuation signature. -/
theorem costStaticEquationDecl_mapCostStaticGenerated_wellSorted
    (source : CIGSLT) (sourceColor targetColor : CostStaticColor)
    (equation : Equation)
    (membership : equation ∈
      source.theory.presentation.presentation.language.equations) :
    EquationWellSorted source.costContinuationRetyping.generatedLanguage
      (match targetColor with
      | .base => costBaseEquation
          (costStaticEquationDecl source sourceColor equation)
      | .wrapped => costWrappedEquation source.costIGSLT
          (costStaticEquationDecl source sourceColor equation)) := by
  rcases source.costStaticEquationDecl_wellSortedWithConstructors
      sourceColor equation membership with
    ⟨type, leftTyped, rightTyped⟩
  have leftMapped :=
    leftTyped.mapCostStaticGenerated source.costContinuationRetyping
      targetColor
  have rightMapped :=
    rightTyped.mapCostStaticGenerated source.costContinuationRetyping
      targetColor
  cases targetColor with
  | base =>
      refine ⟨mapTypeExpr
          (CostStaticColor.base.symbolsOf source.costIGSLT) type, ?_, ?_⟩
      · simpa [costBaseEquation, mapEquation,
          CostStaticColor.symbolsOf,
          WellSorted.FreeTypeContext.ofList_mapTypeContext] using leftMapped
      · simpa [costBaseEquation, mapEquation,
          CostStaticColor.symbolsOf,
          WellSorted.FreeTypeContext.ofList_mapTypeContext] using rightMapped
  | wrapped =>
      refine ⟨mapTypeExpr
          (CostStaticColor.wrapped.symbolsOf source.costIGSLT) type, ?_, ?_⟩
      · simpa [costWrappedEquation, mapEquation,
          CostStaticColor.symbolsOf,
          WellSorted.FreeTypeContext.ofList_mapTypeContext] using leftMapped
      · simpa [costWrappedEquation, mapEquation,
          CostStaticColor.symbolsOf,
          WellSorted.FreeTypeContext.ofList_mapTypeContext] using rightMapped

/-- The complete static equation theory generated by `Cost` satisfies the
same premise, instantiation, matching, and two-color typing obligations
required for another Cost layer. -/
theorem costEquationsRetypable (source : CIGSLT) :
    EquationsRetypable source.costContinuationRetyping := by
  intro generated membership
  change generated ∈ source.costWholeLanguage.equations at membership
  rw [source.costWholeLanguage_equations] at membership
  simp only [costStaticEquations, List.mem_append] at membership
  rcases membership with baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨equation, sourceMembership, rfl⟩
    have sourceRetypable :=
      source.equationsRetypable equation sourceMembership
    refine
      { premiseFree := ?_
        leftInstantiationStable := ?_
        rightInstantiationStable := ?_
        leftMatchCorrect := ?_
        rightMatchCorrect := ?_
        baseWellSorted :=
          source.costStaticEquationDecl_mapCostStaticGenerated_wellSorted
            .base .base equation sourceMembership
        wrappedWellSorted :=
          source.costStaticEquationDecl_mapCostStaticGenerated_wellSorted
            .base .wrapped equation sourceMembership }
    · simp [costBaseEquationDecl_premises, sourceRetypable.premiseFree]
    · simpa [costBaseEquationDecl, mapEquationSchemaNames,
        costBaseEquation, mapEquation] using
          sourceRetypable.leftInstantiationStable
    · simpa [costBaseEquationDecl, mapEquationSchemaNames,
        costBaseEquation, mapEquation] using
          sourceRetypable.rightInstantiationStable
    · simpa [costBaseEquationDecl, mapEquationSchemaNames,
        costBaseEquation, mapEquation] using sourceRetypable.leftMatchCorrect
    · simpa [costBaseEquationDecl, mapEquationSchemaNames,
        costBaseEquation, mapEquation] using sourceRetypable.rightMatchCorrect
  · rcases List.mem_map.mp wrappedMembership with
      ⟨equation, sourceMembership, rfl⟩
    have sourceRetypable :=
      source.equationsRetypable equation sourceMembership
    refine
      { premiseFree := ?_
        leftInstantiationStable := ?_
        rightInstantiationStable := ?_
        leftMatchCorrect := ?_
        rightMatchCorrect := ?_
        baseWellSorted :=
          source.costStaticEquationDecl_mapCostStaticGenerated_wellSorted
            .wrapped .base equation sourceMembership
        wrappedWellSorted :=
          source.costStaticEquationDecl_mapCostStaticGenerated_wellSorted
            .wrapped .wrapped equation sourceMembership }
    · simp [costWrappedEquationDecl_premises,
        sourceRetypable.premiseFree]
    · simpa [costWrappedEquationDecl, mapEquationSchemaNames,
        costWrappedEquation, mapEquation] using
          sourceRetypable.leftInstantiationStable
    · simpa [costWrappedEquationDecl, mapEquationSchemaNames,
        costWrappedEquation, mapEquation] using
          sourceRetypable.rightInstantiationStable
    · simpa [costWrappedEquationDecl, mapEquationSchemaNames,
        costWrappedEquation, mapEquation] using
          sourceRetypable.leftMatchCorrect
    · simpa [costWrappedEquationDecl, mapEquationSchemaNames,
        costWrappedEquation, mapEquation] using
          sourceRetypable.rightMatchCorrect

/-- Exact object laws for one explicitly selected Cost normalizer.

The inherited bundle supplies a sound and complete contextual section.  The
additional field states preservation of the constructor fragment needed by
the next continuation layer.  Neither the source calculus nor the
normalization algorithm is fixed by this interface. -/
structure CostOneObjectLawsFor (source : CIGSLT)
    (normalizeOpen : CostOpenNormalizer source) : Prop
    extends CostOpenSectionLawsFor source normalizeOpen where
  preservesWrappedConstructorTyping :
    ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        source.costWholeReflectionProfile source.costWholeLanguage free bound
          sort),
    WellSorted.HasTypeWithConstructors source.costWholeLanguage
        (· ∈ source.costContinuationRetyping.wrappedLabels)
        free bound term.1 (.base sort.1) →
      WellSorted.HasTypeWithConstructors source.costWholeLanguage
        (· ∈ source.costContinuationRetyping.wrappedLabels)
        free bound (@normalizeOpen free bound sort term).1 (.base sort.1)

/-- Assemble the complete one-step Cost object law around one static kernel.

The executor is fixed by the generic child-first tree traversal.  Unary
soundness comes from one-frame normalization plus weakening, while exact
generator invariance comes from proof-relevant endpoint alignment and compact
chooser coherence.  Contextuality and preservation of the next wrapped
constructor fibre remain separate whole-executor obligations because neither
follows from the local equation law. -/
def CostOneObjectLawsFor.ofStaticKernel
    {source : CIGSLT} (kernel : CostStaticNormalizationKernel source)
    (typed : CostTypedStaticRegionNormalizerLaws source kernel.normalize)
    (contextual : CostContextualOpenLawsFor source
      (fun term => source.costNormalizeOpenWithStatic kernel.normalize term))
    (alignable : CostOpenGeneratorTreeAlignable source kernel)
    (coherent : CostStaticRegionNormalizerCompactCoherent source
      kernel.normalize)
    (preservesWrappedConstructorTyping :
      ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
        {sort : LangSort source.costWholeLanguage}
        (term : ReflectiveWellSorted.OpenTerm
          source.costWholeReflectionProfile source.costWholeLanguage free bound
            sort),
      WellSorted.HasTypeWithConstructors source.costWholeLanguage
          (· ∈ source.costContinuationRetyping.wrappedLabels)
          free bound term.1 (.base sort.1) →
        WellSorted.HasTypeWithConstructors source.costWholeLanguage
          (· ∈ source.costContinuationRetyping.wrappedLabels)
          free bound
            (source.costNormalizeOpenWithStatic kernel.normalize term).1
            (.base sort.1)) :
    CostOneObjectLawsFor source
      (fun term => source.costNormalizeOpenWithStatic kernel.normalize term) where
  toCostOpenSectionLawsFor :=
    { toCostContextualOpenLawsFor := contextual
      equivalent := by
        intro free bound sort term
        exact source.costNormalizeOpenWithStatic_typed_openEquationSetoid
          kernel.normalize typed term
      generatorInvariant :=
        CostOpenGeneratorInvariantFor.forCostNormalizeOpenWithStatic alignable
          coherent }
  preservesWrappedConstructorTyping := preservesWrappedConstructorTyping

/-- A parameterized Cost section preserves the continuation constructor
fragment exactly when its object law says it does. -/
theorem costContextualOpenSectionWith_preservesWrappedConstructorTyping
    (source : CIGSLT) (normalizeOpen : CostOpenNormalizer source)
    (laws : CostOneObjectLawsFor source normalizeOpen) :
    (source.costContextualOpenSectionWith normalizeOpen
      laws.toCostOpenSectionLawsFor).PreservesTypedConstructors
        (· ∈ source.costContinuationRetyping.wrappedLabels) := by
  intro free bound sort term supported
  exact laws.preservesWrappedConstructorTyping term supported

/-- One application of Cost over an arbitrary lawful normalizer.  All
generated syntax and structural fields still come from the sole declaration
construction; only the open-section implementation is parameterized. -/
def costCIGSLTWith (source : CIGSLT)
    (normalizeOpen : CostOpenNormalizer source)
    (laws : CostOneObjectLawsFor source normalizeOpen) : CIGSLT where
  theory := source.costIGSLT
  reflection := source.costWholeAdmittedReflection
  cut := source.costInteractionCut
  openCanonical :=
    source.costContextualOpenSectionWith normalizeOpen
      laws.toCostOpenSectionLawsFor
  continuationRetyping := source.costContinuationRetyping
  bareCollectionConstructorsWrapped :=
    source.costBareCollectionConstructorsWrapped
  openCanonicalPreservesWrappedConstructorTyping :=
    source.costContextualOpenSectionWith_preservesWrappedConstructorTyping
      normalizeOpen laws
  equationsRetypable := source.costEquationsRetypable
  reflectivePresentationsRetypable :=
    source.costReflectivePresentationsRetypable
  sourceEnvelopeStable := source.costSourceEnvelopeStable
  redexRetypable := source.costRedexRetypable
  wrappable := source.costWrappable

/-- Build the continued Cost object directly from a lawful static kernel.
This is the generic construction used by concrete languages: no rho syntax,
normalizer, or canonicalization theorem occurs in the definition. -/
def costCIGSLTOfStaticKernel
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    (typed : CostTypedStaticRegionNormalizerLaws source kernel.normalize)
    (contextual : CostContextualOpenLawsFor source
      (fun term => source.costNormalizeOpenWithStatic kernel.normalize term))
    (alignable : CostOpenGeneratorTreeAlignable source kernel)
    (coherent : CostStaticRegionNormalizerCompactCoherent source
      kernel.normalize)
    (preservesWrappedConstructorTyping :
      ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
        {sort : LangSort source.costWholeLanguage}
        (term : ReflectiveWellSorted.OpenTerm
          source.costWholeReflectionProfile source.costWholeLanguage free bound
            sort),
      WellSorted.HasTypeWithConstructors source.costWholeLanguage
          (· ∈ source.costContinuationRetyping.wrappedLabels)
          free bound term.1 (.base sort.1) →
        WellSorted.HasTypeWithConstructors source.costWholeLanguage
          (· ∈ source.costContinuationRetyping.wrappedLabels)
          free bound
            (source.costNormalizeOpenWithStatic kernel.normalize term).1
            (.base sort.1)) :
    CIGSLT :=
  source.costCIGSLTWith
    (fun term => source.costNormalizeOpenWithStatic kernel.normalize term)
    (CostOneObjectLawsFor.ofStaticKernel kernel typed contextual alignable
      coherent preservesWrappedConstructorTyping)

/-- Exact object laws for the initial strict Cost₁ domain.

The inherited bundle supplies typed unary soundness, an exact section for the
chosen compact executor, and contextual support/naturality.  It deliberately
does not require every proof-relevant elaboration to have the same compact
normal form; that stronger factorization law is not hereditary under Cost
iteration.  The additional field is placed here because it refers to the
generated continuation plan, which is defined only after the region
normalizer. -/
structure CostOneObjectLaws (source : CIGSLT) : Prop
    extends CostOpenSectionLaws source where
  preservesWrappedConstructorTyping :
    ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        source.costWholeReflectionProfile source.costWholeLanguage free bound
          sort),
    WellSorted.HasTypeWithConstructors source.costWholeLanguage
        (· ∈ source.costContinuationRetyping.wrappedLabels)
        free bound term.1 (.base sort.1) →
      WellSorted.HasTypeWithConstructors source.costWholeLanguage
        (· ∈ source.costContinuationRetyping.wrappedLabels)
        free bound (source.costNormalizeOpen term).1 (.base sort.1)

/-- The established compact-executor object law is the specialization of the
generic object law to `costNormalizeOpen`. -/
def CostOneObjectLaws.toCostOneObjectLawsFor
    {source : CIGSLT} (laws : CostOneObjectLaws source) :
    CostOneObjectLawsFor source source.costNormalizeOpen where
  toCostOpenSectionLawsFor :=
    laws.toCostOpenSectionLaws.toCostOpenSectionLawsFor
  preservesWrappedConstructorTyping := by
    intro free bound sort term supported
    exact laws.preservesWrappedConstructorTyping term supported

/-- The generated contextual section preserves the exact hereditary
constructor fragment selected by the next continuation retyping plan. -/
theorem costContextualOpenSection_preservesWrappedConstructorTyping
    (source : CIGSLT) (laws : CostOneObjectLaws source) :
    (source.costContextualOpenSection laws.toCostOpenSectionLaws
      ).PreservesTypedConstructors
        (· ∈ source.costContinuationRetyping.wrappedLabels) := by
  exact source.costContextualOpenSectionWith_preservesWrappedConstructorTyping
    source.costNormalizeOpen laws.toCostOneObjectLawsFor

/-- One application of Cost as a genuine continued interactive GSLT.
Every field is either derived from the sole generated `LanguageDef` or is an
explicit law of the strict Cost₁ object domain. -/
def costCIGSLT (source : CIGSLT) (laws : CostOneObjectLaws source) :
    CIGSLT :=
  source.costCIGSLTWith source.costNormalizeOpen
    laws.toCostOneObjectLawsFor

end CIGSLT

/-! ## The strict canonical-order domain

Exact raw representatives require more than injectivity of canonical keys:
the selected structural order must also be preserved.  The following
category keeps every continued object but restricts arrows to precisely those
continued morphisms that preserve the collision-free structural order.
Exact Cost objects then form an ordinary full subcategory of this category. -/

namespace CIGSLT

/-- Collision-free structural code of a canonical key.  The proof component
of the key contributes no data. -/
def canonicalKeyCode (source : CIGSLT) (key : source.CanonicalKey) : Nat :=
  patternCode key.1.1

/-- Structural coding distinguishes canonical keys exactly. -/
theorem canonicalKeyCode_injective (source : CIGSLT) :
    Function.Injective source.canonicalKeyCode := by
  intro first second equality
  apply Subtype.ext
  apply Subtype.ext
  exact patternCode_injective equality

/-- The canonical-key order used by strict Cost₁ is the collision-free
structural order on normalized authored patterns. -/
instance canonicalKeyLinearOrder (source : CIGSLT) :
    LinearOrder source.CanonicalKey :=
  LinearOrder.lift' source.canonicalKeyCode source.canonicalKeyCode_injective

end CIGSLT

/-- Continued interactive GSLTs equipped with the fixed structural order on
their exact canonical keys.  No new syntax or semantic authority is added. -/
structure OrderedCIGSLT where
  toCIGSLT : CIGSLT

namespace OrderedCIGSLT

instance : CoeSort OrderedCIGSLT Type :=
  ⟨fun source => source.toCIGSLT.CanonicalKey⟩

/-- An ordered continued morphism is an existing continued morphism whose
canonical-key action is monotone for the collision-free structural order. -/
structure Morphism (source target : OrderedCIGSLT) where
  underlying : CIGSLT.Morphism source.toCIGSLT target.toCIGSLT
  canonicalKeyMonotone :
    Monotone (CIGSLT.Morphism.canonicalKeyMap underlying)

namespace Morphism

/-- Ordered continued morphisms are determined by their continued map. -/
@[ext]
theorem ext {source target : OrderedCIGSLT}
    {first second : Morphism source target}
    (underlying : first.underlying = second.underlying) :
    first = second := by
  cases first
  cases second
  cases underlying
  rfl

/-- Identity preserves the structural canonical-key order. -/
def id (source : OrderedCIGSLT) : Morphism source source where
  underlying := CIGSLT.Morphism.id source.toCIGSLT
  canonicalKeyMonotone := by
    intro first second lessOrEqual
    rw [CIGSLT.Morphism.canonicalKeyMap_id,
      CIGSLT.Morphism.canonicalKeyMap_id]
    exact lessOrEqual

/-- Composition preserves structural canonical-key monotonicity. -/
def comp {first second third : OrderedCIGSLT}
    (left : Morphism first second) (right : Morphism second third) :
    Morphism first third where
  underlying := CIGSLT.Morphism.comp left.underlying right.underlying
  canonicalKeyMonotone := by
    intro firstKey secondKey lessOrEqual
    have mapped :=
      right.canonicalKeyMonotone
        (left.canonicalKeyMonotone lessOrEqual)
    change
      CIGSLT.Morphism.canonicalKeyMap
          (CIGSLT.Morphism.comp left.underlying right.underlying) firstKey ≤
        CIGSLT.Morphism.canonicalKeyMap
          (CIGSLT.Morphism.comp left.underlying right.underlying) secondKey
    rw [CIGSLT.Morphism.canonicalKeyMap_comp left.underlying right.underlying,
      CIGSLT.Morphism.canonicalKeyMap_comp left.underlying right.underlying]
    exact mapped

end Morphism

instance : CategoryTheory.Category OrderedCIGSLT where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  id_comp morphism := by
    apply Morphism.ext
    apply CIGSLT.Morphism.ext
    · rfl
    · rfl
  comp_id morphism := by
    apply Morphism.ext
    apply CIGSLT.Morphism.ext
    · rfl
    · rfl
  assoc first second third := by
    apply Morphism.ext
    apply CIGSLT.Morphism.ext
    · rfl
    · rfl

/-- Forget only the canonical-order preservation proof. -/
def forget : CategoryTheory.Functor OrderedCIGSLT CIGSLT where
  obj source := source.toCIGSLT
  map morphism := morphism.underlying
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Exact typed Cost objects inside the strict ordered continued category. -/
def costOneObjectProperty : CategoryTheory.ObjectProperty OrderedCIGSLT :=
  fun source => CIGSLT.CostOneObjectLaws source.toCIGSLT

/-- The honest initial domain for strict Cost₁: arrows preserve key order by
the ambient category, and objects carry the exact typed canonical laws. -/
abbrev CostOneObjects :=
  costOneObjectProperty.FullSubcategory

/-- Forget exact Cost laws and retain the ordered continued object. -/
def costOneObjectsForget :
    CategoryTheory.Functor CostOneObjects OrderedCIGSLT :=
  costOneObjectProperty.ι

end OrderedCIGSLT

end Mettapedia.GSLT.LanguageDef
