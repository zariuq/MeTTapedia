import Mettapedia.GSLT.LanguageDef.CostEndofunctor

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism
open WellSorted
open ContinuationRetypingPlan

namespace CIGSLT

mutual
  theorem test_sourceConstructorsWithin_of_wrappedHasType
      {theory : IGSLT} {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut)
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : WellSorted.HasType plan.generatedLanguage
        free bound
        (mapPattern (CostStaticColor.wrapped.symbolsOf theory) pattern)
        type) :
      ConstructorsWithin (· ∈ plan.wrappedLabels) pattern := by
    induction pattern using Pattern.inductionOn generalizing free bound type with
    | hbvar index => trivial
    | hfvar name => trivial
    | happly constructor arguments inductionHypothesis =>
        generalize patternEquality :
            mapPattern
                (CostStaticColor.wrapped.symbolsOf theory)
                (.apply constructor arguments) = mappedPattern at typed
        cases typed <;> simp [mapPattern] at patternEquality
        case constructor rule arguments' membership notBare argumentsTyped =>
            rcases patternEquality with
              ⟨mappedLabelEquality, argumentsEquality⟩
            change costWrappedConstructorName constructor = rule.label at mappedLabelEquality
            have sourceArgumentsTyped :
                WellSorted.ArgumentsHaveTypes plan.generatedLanguage
                  free bound
                  (arguments.map
                    (mapPattern
                      (CostStaticColor.wrapped.symbolsOf theory)))
                  rule.params := by
              rw [argumentsEquality]
              exact argumentsTyped
            constructor
            · simp only [ContinuationRetypingPlan.generatedLanguage,
                List.mem_append, List.mem_map] at membership
              rcases membership with
                ⟨sourceRule, sourceMembership, equality⟩ |
                ⟨wrappedRule, wrappedMembership, equality⟩
              · have generatedLabelEquality :=
                  congrArg GrammarRule.label equality
                exact False.elim
                  (costBaseConstructorName_ne_wrapped
                    sourceRule.label constructor
                    (generatedLabelEquality.trans mappedLabelEquality.symm))
              · have generatedLabelEquality :=
                  congrArg GrammarRule.label equality
                have sourceLabelEquality :
                    wrappedRule.1.label = constructor :=
                  costWrappedConstructorName_injective
                    (generatedLabelEquality.trans mappedLabelEquality.symm)
                exact List.mem_map.mpr
                  ⟨wrappedRule, wrappedMembership, sourceLabelEquality⟩
            · exact
                test_sourceConstructorListWithin_of_wrappedArgumentsHaveTypes
                  plan sourceArgumentsTyped inductionHypothesis
    | hlambda binder body inductionHypothesis =>
        cases typed with
        | lambda bodyTyped => exact inductionHypothesis bodyTyped
    | hmultiLambda arity binders body inductionHypothesis =>
        cases typed with
        | multiLambda bodyTyped => exact inductionHypothesis bodyTyped
    | hsubst body replacement bodyInduction replacementInduction =>
        cases typed with
        | subst bodyTyped replacementTyped =>
            exact ⟨bodyInduction bodyTyped, replacementInduction replacementTyped⟩
    | hcollection collectionType elements rest inductionHypothesis =>
        cases typed with
        | collection elementsTyped =>
            exact
              test_sourceConstructorListWithin_of_wrappedElementsHaveType
                plan (by simpa [mapPatternList_eq_map] using elementsTyped)
                  inductionHypothesis
        | collectionConstructor membership parameterShape elementsTyped =>
            exact
              test_sourceConstructorListWithin_of_wrappedElementsHaveType
                plan (by simpa [mapPatternList_eq_map] using elementsTyped)
                  inductionHypothesis

  theorem test_sourceConstructorListWithin_of_wrappedArgumentsHaveTypes
      {theory : IGSLT} {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut)
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypes plan.generatedLanguage
        free bound
        (patterns.map
          (mapPattern (CostStaticColor.wrapped.symbolsOf theory)))
        parameters)
      (inductionHypothesis : ∀ pattern ∈ patterns,
        ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
          {type : TypeExpr},
          WellSorted.HasType plan.generatedLanguage free bound
            (mapPattern (CostStaticColor.wrapped.symbolsOf theory) pattern)
            type →
          ConstructorsWithin (· ∈ plan.wrappedLabels) pattern) :
      ConstructorListWithin (· ∈ plan.wrappedLabels) patterns := by
    induction patterns generalizing parameters with
    | nil => trivial
    | cons pattern patterns tailInduction =>
        cases typed with
        | cons representation parameterType headTyped tailTyped =>
            exact
              ⟨inductionHypothesis pattern (by simp) headTyped,
                tailInduction tailTyped
                  (fun nested membership =>
                    inductionHypothesis nested (by simp [membership]))⟩

  theorem test_sourceConstructorListWithin_of_wrappedElementsHaveType
      {theory : IGSLT} {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut)
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {type : TypeExpr}
      (typed : WellSorted.ElementsHaveType plan.generatedLanguage
        free bound
        (patterns.map
          (mapPattern (CostStaticColor.wrapped.symbolsOf theory)))
        type)
      (inductionHypothesis : ∀ pattern ∈ patterns,
        ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
          {type : TypeExpr},
          WellSorted.HasType plan.generatedLanguage free bound
            (mapPattern (CostStaticColor.wrapped.symbolsOf theory) pattern)
            type →
          ConstructorsWithin (· ∈ plan.wrappedLabels) pattern) :
      ConstructorListWithin (· ∈ plan.wrappedLabels) patterns := by
    induction patterns with
    | nil => trivial
    | cons pattern patterns tailInduction =>
        cases typed with
        | cons headTyped tailTyped =>
            exact
              ⟨inductionHypothesis pattern (by simp) headTyped,
                tailInduction tailTyped
                  (fun nested membership =>
                    inductionHypothesis nested (by simp [membership]))⟩
end

theorem test_costStaticConstructorLabel_mem_costContinuationLabels_of_mem
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

theorem test_costStaticSchemaPattern_constructorsWithin
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
      test_costStaticConstructorLabel_mem_costContinuationLabels_of_mem
        source color constructor membership
  · exact supported

theorem test_costStaticEquationDecl_wellSortedWithConstructors
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
    test_costStaticSchemaPattern_constructorsWithin source color
      sourceLeftSupported
  have rightSupported :=
    test_costStaticSchemaPattern_constructorsWithin source color
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

theorem test_costStaticEquationDecl_mapCostStaticGenerated_wellSorted
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
  rcases
      test_costStaticEquationDecl_wellSortedWithConstructors
        source sourceColor equation membership with
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

mutual
  @[simp]
  theorem test_hasCanonicalBinderMetadata_mapPatternSchemaNames
      (mapName : String → String) (pattern : Pattern) :
      (mapPatternSchemaNames mapName pattern).hasCanonicalBinderMetadata =
        pattern.hasCanonicalBinderMetadata := by
    cases pattern <;>
      simp [mapPatternSchemaNames, Pattern.hasCanonicalBinderMetadata,
        test_hasCanonicalBinderMetadata_mapPatternSchemaNames,
        test_hasCanonicalBinderMetadataList_mapPatternSchemaNames]

  @[simp]
  theorem test_hasCanonicalBinderMetadataList_mapPatternSchemaNames
      (mapName : String → String) (patterns : List Pattern) :
      Pattern.hasCanonicalBinderMetadataList
          (mapPatternListSchemaNames mapName patterns) =
        Pattern.hasCanonicalBinderMetadataList patterns := by
    cases patterns <;>
      simp [mapPatternListSchemaNames, Pattern.hasCanonicalBinderMetadataList,
        test_hasCanonicalBinderMetadata_mapPatternSchemaNames,
        test_hasCanonicalBinderMetadataList_mapPatternSchemaNames]
end

mutual
  @[simp]
  theorem test_schemaHasNoCollectionRest_mapPatternSchemaNames
      (mapName : String → String) (pattern : Pattern) :
      schemaHasNoCollectionRest (mapPatternSchemaNames mapName pattern) =
        schemaHasNoCollectionRest pattern := by
    cases pattern <;>
      simp [mapPatternSchemaNames, schemaHasNoCollectionRest,
        test_schemaHasNoCollectionRest_mapPatternSchemaNames,
        test_schemaListHasNoCollectionRest_mapPatternSchemaNames]

  @[simp]
  theorem test_schemaListHasNoCollectionRest_mapPatternSchemaNames
      (mapName : String → String) (patterns : List Pattern) :
      schemaListHasNoCollectionRest
          (mapPatternListSchemaNames mapName patterns) =
        schemaListHasNoCollectionRest patterns := by
    cases patterns <;>
      simp [mapPatternListSchemaNames, schemaListHasNoCollectionRest,
        test_schemaHasNoCollectionRest_mapPatternSchemaNames,
        test_schemaListHasNoCollectionRest_mapPatternSchemaNames]
end

@[simp]
theorem test_schemaInstantiationStable_mapPatternSchemaNames
    (mapName : String → String) (pattern : Pattern) :
    schemaInstantiationStable (mapPatternSchemaNames mapName pattern) =
      schemaInstantiationStable pattern := by
  simp [schemaInstantiationStable]

mutual
  @[simp]
  theorem test_isMatchCorrectAux_mapPatternSchemaNames
      (mapName : String → String) (pattern : Pattern) :
      Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectAux
          (mapPatternSchemaNames mapName pattern) =
        Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectAux pattern := by
    cases pattern <;>
      simp [mapPatternSchemaNames,
        Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectAux,
        test_isMatchCorrectListAux_mapPatternSchemaNames]

  @[simp]
  theorem test_isMatchCorrectListAux_mapPatternSchemaNames
      (mapName : String → String) (patterns : List Pattern) :
      Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectListAux
          (mapPatternListSchemaNames mapName patterns) =
        Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectListAux patterns := by
    cases patterns <;>
      simp [mapPatternListSchemaNames,
        Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectListAux,
        test_isMatchCorrectAux_mapPatternSchemaNames,
        test_isMatchCorrectListAux_mapPatternSchemaNames]
end

@[simp]
theorem test_isMatchCorrect_mapPatternSchemaNames
    (mapName : String → String) (pattern : Pattern) :
    Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect
        (mapPatternSchemaNames mapName pattern) =
      Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect pattern :=
  test_isMatchCorrectAux_mapPatternSchemaNames mapName pattern

theorem test_costEquationsRetypable (source : CIGSLT) :
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
          test_costStaticEquationDecl_mapCostStaticGenerated_wellSorted
            source .base .base equation sourceMembership
        wrappedWellSorted :=
          test_costStaticEquationDecl_mapCostStaticGenerated_wellSorted
            source .base .wrapped equation sourceMembership }
    · simpa [costBaseEquationDecl_premises, sourceRetypable.premiseFree]
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
          test_costStaticEquationDecl_mapCostStaticGenerated_wellSorted
            source .wrapped .base equation sourceMembership
        wrappedWellSorted :=
          test_costStaticEquationDecl_mapCostStaticGenerated_wellSorted
            source .wrapped .wrapped equation sourceMembership }
    · simpa [costWrappedEquationDecl_premises,
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

theorem test_matchesParameterRepresentation_mixed_map_iff
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
  theorem test_mapCostBaseImageClosure
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
                  rule.params := by
              exact argumentsTyped
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
                test_mapCostBaseImageClosureArguments source
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
              (HasType.lambda (inductionHypothesis bodyTyped))
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
              test_mapCostBaseImageClosureElements source
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
              test_mapCostBaseImageClosureElements source
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
              change targetRule.params =
                [.simple parameterName
                  (.collection collectionType
                    (mapTypeExpr source.costClosureSymbols elementType))]
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

  theorem test_mapCostBaseImageClosureArguments
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
                    (mapPattern costBasePresentationSymbols pattern)) := by
              exact
                (test_matchesParameterRepresentation_mixed_map_iff
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

  theorem test_mapCostBaseImageClosureElements
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

theorem test_costBaseMappedRedex_retyped (source : CIGSLT) :
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
    test_mapCostBaseImageClosure source source.redexRetypable
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

theorem test_costApparatusConstructor_not_selected
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

theorem test_costBaseConstructor_params_eq_map_of_notSelected
    (cut : InteractionCutPresentation source)
    (rule : GrammarRule)
    (notSelected : ∀ index,
      isSelectedContinuation cut rule index = false) :
    (costBaseConstructor cut rule).params =
      rule.params.map (mapParameterType costBaseTypeExpr) := by
  apply List.ext_getElem
  · simpa using costBaseConstructor_params_length cut rule
  · intro index leftBounds rightBounds
    have sourceBounds : index < rule.params.length := by
      simpa using rightBounds
    rw [costBaseConstructor_parameter cut rule index sourceBounds,
      List.getElem_map]
    unfold costBaseParameter
    rw [notSelected index]
    simp

theorem test_costNextSignatureVariable_hasType (source : CIGSLT) :
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

theorem test_costNextStackTailVariable_hasType (source : CIGSLT) :
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

theorem test_costBaseApparatusConstructor_mem_generated
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

theorem test_costNextSigned_hasType (source : CIGSLT) {body : Pattern}
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
    rw [test_costBaseConstructor_params_eq_map_of_notSelected
      source.costInteractionCut rule
      (test_costApparatusConstructor_not_selected source rule "signed" rfl)]
    simp [rule, costSignedConstructor, mapParameterType,
      costBaseTypeExpr]
  have target :=
    HasType.constructor
      (test_costBaseApparatusConstructor_mem_generated source rule
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
            (test_costNextSignatureVariable_hasType source) .nil))
  simpa [rule, costBaseConstructor, costSignedConstructor] using target

theorem test_costNextTokenStackCons_hasType (source : CIGSLT) :
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
    rw [test_costBaseConstructor_params_eq_map_of_notSelected
      source.costInteractionCut rule
      (test_costApparatusConstructor_not_selected source rule
        "token-stack-cons" rfl)]
    simp [rule, costTokenStackConsConstructor, mapParameterType,
      costBaseTypeExpr]
  have target :=
    HasType.constructor
      (test_costBaseApparatusConstructor_mem_generated source rule
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
          (test_costNextSignatureVariable_hasType source)
          (.cons trivial rfl
            (test_costNextStackTailVariable_hasType source) .nil))
  simpa [rule, costBaseConstructor, costTokenStackConsConstructor] using
    target

theorem test_costNextFunding_hasType (source : CIGSLT) {stack : Pattern}
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
    rw [test_costBaseConstructor_params_eq_map_of_notSelected
      source.costInteractionCut rule
      (test_costApparatusConstructor_not_selected source rule "funding" rfl)]
    simp [rule, costFundingConstructor, mapParameterType,
      costBaseTypeExpr]
  have target :=
    HasType.constructor
      (test_costBaseApparatusConstructor_mem_generated source rule
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

theorem test_costNextContact_hasType (source : CIGSLT)
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
    rw [test_costBaseConstructor_params_eq_map_of_notSelected
      source.costInteractionCut rule
      (test_costApparatusConstructor_not_selected source rule "contact" rfl)]
    simp [rule, costContactConstructor, mapParameterType,
      costBaseTypeExpr]
  have target :=
    HasType.constructor
      (test_costBaseApparatusConstructor_mem_generated source rule
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

theorem test_costRedexRetypable (source : CIGSLT) :
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
    test_costNextContact_hasType source
      (test_costNextSigned_hasType source
        (test_costBaseMappedRedex_retyped source))
      (test_costNextFunding_hasType source
        (test_costNextTokenStackCons_hasType source))

end CIGSLT

end Mettapedia.GSLT.LanguageDef

#print axioms
  Mettapedia.GSLT.LanguageDef.CIGSLT.costReflectivePresentationsRetypable
#print axioms Mettapedia.GSLT.LanguageDef.CIGSLT.costCIGSLT
