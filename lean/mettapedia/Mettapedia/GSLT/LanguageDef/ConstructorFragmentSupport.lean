import Mettapedia.GSLT.LanguageDef.ConstructorFragmentTyping
import Mettapedia.GSLT.LanguageDef.ContextSupport

/-!
# Reflective support under declaration-fragment transport

Exact target row witnesses and preservation of the quote classifier suffice
to transport support through an authored constructor fragment. Target support
lists are kept fixed; the source binder image records the static type map.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Reflection
namespace WellSorted


mutual
  /-- Row-wise static transport retains the exact declared support context. -/
  theorem HasType.ReflectiveSupportSafeAt.mapRows
      {source target : LanguageDef} {allowed : String → Prop}
      (symbols : LanguageDefSymbolMap)
      (rows : ∀ rule ∈ source.terms, allowed rule.label →
        ∃ targetRule ∈ target.terms,
          targetRule.label = symbols.constructor rule.label ∧
          targetRule.category = symbols.sort rule.category ∧
          targetRule.params = rule.params.map (mapTermParam symbols))
      (bareAllowed : ∀ rule ∈ source.terms, UsesBareCollection rule → allowed rule.label)
      {sourceReflection targetReflection : ReflectionProfile}
      (quotes : ∀ rule ∈ source.terms, allowed rule.label →
        ReflectiveContextSupport.isQuoteConstructor targetReflection (symbols.constructor rule.label) =
          ReflectiveContextSupport.isQuoteConstructor sourceReflection rule.label)
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : HasType source free bound pattern type}
      {support : ContextSupport.Support} {available : List TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt sourceReflection support available (mapTypeExpr symbols))
      (supported : ConstructorsWithin allowed pattern) :
      ∃ targetTyped : HasType target (free.map symbols) (bound.map (mapTypeExpr symbols))
          (mapPattern symbols pattern) (mapTypeExpr symbols type),
        targetTyped.ReflectiveSupportSafeAt targetReflection support available id := by
    cases safe with
    | @bvar bound index type lookup available _binderImage =>
        have mappedLookup :
            (bound.map (mapTypeExpr symbols))[index]? =
              some (mapTypeExpr symbols type) := by
          simpa using congrArg
            (Option.map (mapTypeExpr symbols)) lookup
        let targetTyped : HasType target
            (free.map symbols)
            (bound.map (mapTypeExpr symbols))
            (.bvar index) (mapTypeExpr symbols type) :=
          HasType.bvar mappedLookup
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            targetReflection support available :=
          .bvar mappedLookup _
        simp only [mapPattern]
        exact ⟨targetTyped, targetSafe⟩
    | @fvar bound name type lookup available _binderImage shape =>
        have mappedLookup :
            (free.map symbols) name =
              some (mapTypeExpr symbols type) := by
          unfold FreeTypeContext.map
          rw [lookup]
          rfl
        let targetTyped := HasType.fvar
          (language := target)
          (bound := bound.map (mapTypeExpr symbols))
          mappedLookup
        simp only [mapPattern]
        refine ⟨targetTyped, .fvar mappedLookup _ ?_⟩
        exact shape
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        available _binderImage classification argumentsSafe =>
        obtain ⟨mappedArguments, mappedArgumentsSafe⟩ := argumentsSafe.mapRows symbols rows bareAllowed quotes (bound := bound) supported.2
        obtain ⟨targetRule, targetMember, targetLabel, targetCategory, targetParams⟩ :=
          rows rule membership supported.1
        have targetArguments : ArgumentsHaveTypes target (free.map symbols)
            (bound.map (mapTypeExpr symbols)) (arguments.map (mapPattern symbols)) targetRule.params := by
          simpa only [targetParams] using mappedArguments
        have targetSafe : targetArguments.ReflectiveSupportSafeAt targetReflection support [] id := by
          simpa only [targetParams] using mappedArgumentsSafe
        have targetNotBare : ¬ UsesBareCollection targetRule := by
          have result := fun bare => notBare ((usesBareCollection_mapGrammarRule_iff symbols rule).mp bare)
          simpa [UsesBareCollection, targetParams, mapGrammarRule] using result
        have classified : ReflectiveContextSupport.isQuoteConstructor targetReflection targetRule.label = true := by
          rw [targetLabel, quotes rule membership supported.1]
          exact classification
        let resultTyped := HasType.constructor targetMember targetNotBare targetArguments
        have resultSafe : resultTyped.ReflectiveSupportSafeAt targetReflection support available id :=
          .constructorQuote (membership := targetMember) (notBare := targetNotBare)
            (argumentsTyped := targetArguments) classified targetSafe
        have result : ∃ targetTyped : HasType target (free.map symbols)
            (bound.map (mapTypeExpr symbols))
            (.apply targetRule.label (arguments.map (mapPattern symbols))) (.base targetRule.category),
            targetTyped.ReflectiveSupportSafeAt targetReflection support available id :=
          ⟨resultTyped, resultSafe⟩
        simpa only [targetLabel, targetCategory, mapPattern, mapPatternList_eq_map, mapTypeExpr] using result
    | @constructorOrdinary bound rule arguments membership notBare argumentsTyped
        available _binderImage classification argumentsSafe =>
        obtain ⟨mappedArguments, mappedArgumentsSafe⟩ := argumentsSafe.mapRows symbols rows bareAllowed quotes (bound := bound) supported.2
        obtain ⟨targetRule, targetMember, targetLabel, targetCategory, targetParams⟩ :=
          rows rule membership supported.1
        have targetArguments : ArgumentsHaveTypes target (free.map symbols)
            (bound.map (mapTypeExpr symbols)) (arguments.map (mapPattern symbols)) targetRule.params := by
          simpa only [targetParams] using mappedArguments
        have targetSafe : targetArguments.ReflectiveSupportSafeAt targetReflection support available id := by
          simpa only [targetParams] using mappedArgumentsSafe
        have targetNotBare : ¬ UsesBareCollection targetRule := by
          have result := fun bare => notBare ((usesBareCollection_mapGrammarRule_iff symbols rule).mp bare)
          simpa [UsesBareCollection, targetParams, mapGrammarRule] using result
        have classified : ReflectiveContextSupport.isQuoteConstructor targetReflection targetRule.label = false := by
          rw [targetLabel, quotes rule membership supported.1]
          exact classification
        let resultTyped := HasType.constructor targetMember targetNotBare targetArguments
        have resultSafe : resultTyped.ReflectiveSupportSafeAt targetReflection support available id :=
          .constructorOrdinary (membership := targetMember) (notBare := targetNotBare)
            (argumentsTyped := targetArguments) classified targetSafe
        have result : ∃ targetTyped : HasType target (free.map symbols)
            (bound.map (mapTypeExpr symbols))
            (.apply targetRule.label (arguments.map (mapPattern symbols))) (.base targetRule.category),
            targetTyped.ReflectiveSupportSafeAt targetReflection support available id :=
          ⟨resultTyped, resultSafe⟩
        simpa only [targetLabel, targetCategory, mapPattern, mapPatternList_eq_map, mapTypeExpr] using result
    | @lambda bound binder body domain codomain bodyTyped available
        _binderImage bodySafe =>
        obtain ⟨mappedBody, mappedBodySafe⟩ :=
          bodySafe.mapRows symbols rows bareAllowed quotes (bound := domain :: bound) supported
        have mappedBodySafe' :
            mappedBody.ReflectiveSupportSafeAt
              targetReflection support
              (mapTypeExpr symbols domain :: available) :=
          mappedBodySafe
        let targetTyped := HasType.lambda
          (binder := binder) mappedBody
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            targetReflection support available :=
          .lambda mappedBodySafe'
        simp only [mapPattern, mapTypeExpr]
        exact ⟨targetTyped, targetSafe⟩
    | @multiLambda bound arity binders body domain codomain bodyTyped available
        _binderImage bodySafe =>
        obtain ⟨mappedBody, mappedBodySafe⟩ :=
          bodySafe.mapRows symbols rows bareAllowed quotes
            (bound := List.replicate arity domain ++ bound)
            supported
        have mappedBody' : HasType target
            (free.map symbols)
            (List.replicate arity
                (mapTypeExpr symbols domain) ++
              bound.map (mapTypeExpr symbols))
            (mapPattern symbols body)
            (mapTypeExpr symbols codomain) := by
          simpa [List.map_append, List.map_replicate] using mappedBody
        have mappedBodySafe' : mappedBody'.ReflectiveSupportSafeAt
            targetReflection support
            (List.replicate arity
                (mapTypeExpr symbols domain) ++
              available) :=
          by
            simpa [List.map_append, List.map_replicate] using mappedBodySafe
        let targetTyped := HasType.multiLambda
          (binders := binders) mappedBody'
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            targetReflection support available :=
          .multiLambda mappedBodySafe'
        simp only [mapPattern, mapTypeExpr]
        exact ⟨targetTyped, targetSafe⟩
    | @subst bound body replacement domain codomain bodyTyped replacementTyped
        available _binderImage bodySafe replacementSafe =>
        obtain ⟨mappedBody, mappedBodySafe⟩ :=
          bodySafe.mapRows symbols rows bareAllowed quotes (bound := domain :: bound)
            supported.1
        obtain ⟨mappedReplacement, mappedReplacementSafe⟩ :=
          replacementSafe.mapRows symbols rows bareAllowed quotes (bound := bound)
            supported.2
        have mappedBodySafe' :
            mappedBody.ReflectiveSupportSafeAt
              targetReflection support
              (mapTypeExpr symbols domain :: available) :=
          mappedBodySafe
        let targetTyped := HasType.subst mappedBody mappedReplacement
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            targetReflection support available :=
          .subst mappedBodySafe' mappedReplacementSafe
        simp only [mapPattern]
        exact ⟨targetTyped, targetSafe⟩
    | @collection bound collectionType elements rest elementType elementsTyped
        available _binderImage elementsSafe =>
        obtain ⟨mappedElements, mappedElementsSafe⟩ :=
          elementsSafe.mapRows symbols rows bareAllowed quotes (bound := bound) supported
        let targetTyped := HasType.collection
          (collectionType := collectionType) (rest := rest) mappedElements
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            targetReflection support available :=
          .collection mappedElementsSafe
        simp only [mapPattern, mapPatternList_eq_map, mapTypeExpr]
        exact ⟨targetTyped, targetSafe⟩
    | @collectionConstructor bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped available _binderImage elementsSafe =>
        obtain ⟨mappedElements, mappedElementsSafe⟩ := elementsSafe.mapRows symbols rows bareAllowed quotes (bound := bound) supported
        obtain ⟨targetRule, targetMember, targetLabel, targetCategory, targetParams⟩ :=
          rows rule membership (bareAllowed rule membership ⟨_, _, _, parameterShape⟩)
        have targetShape : targetRule.params = [.simple parameterName
            (.collection collectionType (mapTypeExpr symbols elementType))] := by
          simp [targetParams, parameterShape, mapTermParam, mapTypeExpr]
        let resultTyped := HasType.collectionConstructor (rest := rest) targetMember targetShape mappedElements
        have resultSafe : resultTyped.ReflectiveSupportSafeAt targetReflection support available id :=
          .collectionConstructor (membership := targetMember) (parameterShape := targetShape)
            (elementsTyped := mappedElements) mappedElementsSafe
        have result : ∃ targetTyped : HasType target (free.map symbols)
            (bound.map (mapTypeExpr symbols))
            (.collection collectionType (elements.map (mapPattern symbols)) rest) (.base targetRule.category),
            targetTyped.ReflectiveSupportSafeAt targetReflection support available id :=
          ⟨resultTyped, resultSafe⟩
        simpa only [targetCategory, mapPattern, mapPatternList_eq_map, mapTypeExpr] using result

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.mapRows
      {source target : LanguageDef} {allowed : String → Prop}
      (symbols : LanguageDefSymbolMap)
      (rows : ∀ rule ∈ source.terms, allowed rule.label →
        ∃ targetRule ∈ target.terms,
          targetRule.label = symbols.constructor rule.label ∧
          targetRule.category = symbols.sort rule.category ∧
          targetRule.params = rule.params.map (mapTermParam symbols))
      (bareAllowed : ∀ rule ∈ source.terms, UsesBareCollection rule → allowed rule.label)
      {sourceReflection targetReflection : ReflectionProfile}
      (quotes : ∀ rule ∈ source.terms, allowed rule.label →
        ReflectiveContextSupport.isQuoteConstructor targetReflection (symbols.constructor rule.label) =
          ReflectiveContextSupport.isQuoteConstructor sourceReflection rule.label)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      {typed : ArgumentsHaveTypes
        source
        free bound arguments parameters}
      {support : ContextSupport.Support} {available : List TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt sourceReflection support available
        (mapTypeExpr symbols))
      (supported : ConstructorListWithin
        allowed arguments) :
      ∃ targetTyped : ArgumentsHaveTypes target
          (free.map symbols)
          (bound.map (mapTypeExpr symbols))
          (arguments.map (mapPattern symbols))
          (parameters.map (mapTermParam symbols)),
        targetTyped.ReflectiveSupportSafeAt targetReflection
          support available := by
    cases safe with
    | nil =>
        let targetTyped := ArgumentsHaveTypes.nil
          (language := target)
          (free := free.map symbols)
          (bound := bound.map (mapTypeExpr symbols))
        exact ⟨targetTyped, .nil _ _⟩
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        _binderImage argumentSafe argumentsSafe =>
        obtain ⟨mappedArgument, mappedArgumentSafe⟩ :=
          argumentSafe.mapRows symbols rows bareAllowed quotes (bound := bound) supported.1
        obtain ⟨mappedArguments, mappedArgumentsSafe⟩ :=
          argumentsSafe.mapRows symbols rows bareAllowed quotes (bound := bound) supported.2
        have mappedParameterType :
            parameterType?
                (mapTermParam symbols parameter) =
              some (mapTypeExpr symbols expected) := by
          rw [parameterType?_mapTermParam, parameterType]
          rfl
        have mappedRepresentation :
            MatchesParameterRepresentation
              (mapTermParam symbols parameter)
              (mapPattern symbols argument) :=
          (matchesParameterRepresentation_map_iff
            symbols parameter argument).2 representation
        let targetTyped := ArgumentsHaveTypes.cons
          mappedRepresentation
          mappedParameterType mappedArgument mappedArguments
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            targetReflection support available :=
          ArgumentsHaveTypes.ReflectiveSupportSafeAt.cons
            (representation := mappedRepresentation)
            (parameterType := mappedParameterType)
            (argumentTyped := mappedArgument)
            (argumentsTyped := mappedArguments)
            mappedArgumentSafe mappedArgumentsSafe
        exact ⟨targetTyped, targetSafe⟩


  theorem ElementsHaveType.ReflectiveSupportSafeAt.mapRows
      {source target : LanguageDef} {allowed : String → Prop}
      (symbols : LanguageDefSymbolMap)
      (rows : ∀ rule ∈ source.terms, allowed rule.label →
        ∃ targetRule ∈ target.terms,
          targetRule.label = symbols.constructor rule.label ∧
          targetRule.category = symbols.sort rule.category ∧
          targetRule.params = rule.params.map (mapTermParam symbols))
      (bareAllowed : ∀ rule ∈ source.terms, UsesBareCollection rule → allowed rule.label)
      {sourceReflection targetReflection : ReflectionProfile}
      (quotes : ∀ rule ∈ source.terms, allowed rule.label →
        ReflectiveContextSupport.isQuoteConstructor targetReflection (symbols.constructor rule.label) =
          ReflectiveContextSupport.isQuoteConstructor sourceReflection rule.label)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      {typed : ElementsHaveType
        source
        free bound elements elementType}
      {support : ContextSupport.Support} {available : List TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt sourceReflection support available
        (mapTypeExpr symbols))
      (supported : ConstructorListWithin
        allowed elements) :
      ∃ targetTyped : ElementsHaveType target
          (free.map symbols)
          (bound.map (mapTypeExpr symbols))
          (elements.map (mapPattern symbols))
          (mapTypeExpr symbols elementType),
        targetTyped.ReflectiveSupportSafeAt targetReflection
          support available := by
    cases safe with
    | nil =>
        let targetTyped := ElementsHaveType.nil
          (language := target)
          (free := free.map symbols)
          (bound.map (mapTypeExpr symbols))
          (mapTypeExpr symbols elementType)
        exact ⟨targetTyped, .nil _ _ _⟩
    | @cons bound element elements elementType elementTyped elementsTyped
        available _binderImage elementSafe elementsSafe =>
        obtain ⟨mappedElement, mappedElementSafe⟩ :=
          elementSafe.mapRows symbols rows bareAllowed quotes (bound := bound) supported.1
        obtain ⟨mappedElements, mappedElementsSafe⟩ :=
          elementsSafe.mapRows symbols rows bareAllowed quotes (bound := bound) supported.2
        let targetTyped := ElementsHaveType.cons
          mappedElement mappedElements
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            targetReflection support available :=
          ElementsHaveType.ReflectiveSupportSafeAt.cons
            (elementTyped := mappedElement)
            (elementsTyped := mappedElements)
            mappedElementSafe mappedElementsSafe
        exact ⟨targetTyped, targetSafe⟩
end

/-- The constructor-fragment typing map itself carries the transported support.
The bare-row premise covers declaration choices invisible in collection syntax. -/
theorem HasTypeWithConstructors.mapRows_reflectiveSupport
      {source target : LanguageDef} {allowed : String → Prop}
      (symbols : LanguageDefSymbolMap)
      (rows : ∀ rule ∈ source.terms, allowed rule.label →
        ∃ targetRule ∈ target.terms,
          targetRule.label = symbols.constructor rule.label ∧
          targetRule.category = symbols.sort rule.category ∧
          targetRule.params = rule.params.map (mapTermParam symbols))
      (bareAllowed : ∀ rule ∈ source.terms, UsesBareCollection rule → allowed rule.label)
      {sourceReflection targetReflection : ReflectionProfile}
      (quotes : ∀ rule ∈ source.terms, allowed rule.label →
        ReflectiveContextSupport.isQuoteConstructor targetReflection (symbols.constructor rule.label) =
          ReflectiveContextSupport.isQuoteConstructor sourceReflection rule.label)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors source allowed free bound pattern type)
    {support : ContextSupport.Support} {available : List TypeExpr}
    (safe : typed.toHasType.ReflectiveSupportSafeAt sourceReflection support available
      (mapTypeExpr symbols)) :
    (typed.mapRows symbols rows).ReflectiveSupportSafeAt targetReflection support available id := by
  obtain ⟨mapped, mappedSafe⟩ := safe.mapRows symbols rows bareAllowed quotes typed.constructorsWithin
  exact mappedSafe.castTyping

end WellSorted
end Mettapedia.GSLT.LanguageDef
