import Mettapedia.GSLT.LanguageDef.ConstructorSupport

/-!
# Typing transport on a declared constructor fragment

A typing derivation remembers the declaration of a bare collection even when
its label is absent from the raw pattern. Uniform symbol transport therefore
needs row witnesses only for the labels admitted by that derivation. These
lemmas require neither a second language hierarchy nor a map on excluded rows.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism
namespace WellSorted
set_option autoImplicit false

mutual
  /-- Row witnesses on the supported constructor fragment suffice for typing transport. -/
  theorem HasTypeWithConstructors.mapRows
      {source target : LanguageDef} {allowed : String → Prop}
      (symbols : LanguageDefSymbolMap)
      (rows : ∀ rule ∈ source.terms, allowed rule.label →
        ∃ targetRule ∈ target.terms,
          targetRule.label = symbols.constructor rule.label ∧
          targetRule.category = symbols.sort rule.category ∧
          targetRule.params = rule.params.map (mapTermParam symbols))
      {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : HasTypeWithConstructors source allowed free bound pattern type) :
      HasType target (free.map symbols)
        (bound.map (mapTypeExpr symbols))
        (mapPattern symbols pattern)
        (mapTypeExpr symbols type) := by
    cases typed with
    | @bvar bound index type lookup =>
        have mappedLookup :
            (bound.map (mapTypeExpr symbols))[index]?
              = some (mapTypeExpr symbols type) := by
          simpa using congrArg
            (Option.map (mapTypeExpr symbols)) lookup
        simpa [mapPattern] using
          (HasType.bvar (free := free.map symbols) mappedLookup)
    | @fvar bound name type lookup =>
        have mappedLookup :
            (free.map symbols) name =
              some (mapTypeExpr symbols type) := by
          simp [FreeTypeContext.map, lookup]
        simpa [mapPattern] using
          (HasType.fvar (bound := bound.map (mapTypeExpr symbols))
            mappedLookup)
    | @constructor bound rule arguments supported membership notBareCollection argumentsTyped =>
        obtain ⟨targetRule, targetMembership, targetLabel, targetCategory,
          targetParameters⟩ := rows rule membership supported
        have mappedArguments := argumentsTyped.mapRows symbols rows
        have mappedNotBareCollection :
            ¬ UsesBareCollection (mapGrammarRule symbols rule) :=
          fun mappedBare => notBareCollection
            ((usesBareCollection_mapGrammarRule_iff symbols rule).mp
              mappedBare)
        have targetArguments :
            ArgumentsHaveTypes target
              (free.map symbols)
              (bound.map (mapTypeExpr symbols))
              (arguments.map (mapPattern symbols))
              targetRule.params := by
          simpa [targetParameters] using mappedArguments
        simpa [mapPattern, targetLabel, targetCategory, mapTypeExpr] using
          (HasType.constructor
            targetMembership (by
              simpa [UsesBareCollection, targetParameters, mapGrammarRule] using
                mappedNotBareCollection)
            targetArguments)
    | @lambda bound binder body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapRows symbols rows
        simpa [mapPattern, mapTypeExpr] using HasType.lambda mappedBody
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapRows symbols rows
        have mappedBody' :
            HasType target (free.map symbols)
              (List.replicate arity (mapTypeExpr symbols domain) ++
                bound.map (mapTypeExpr symbols))
              (mapPattern symbols body)
              (mapTypeExpr symbols codomain) := by
          simpa [List.map_append, List.map_replicate] using mappedBody
        simpa [mapPattern, mapTypeExpr] using
          HasType.multiLambda mappedBody'
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        have mappedBody := bodyTyped.mapRows symbols rows
        have mappedReplacement := replacementTyped.mapRows symbols rows
        simpa [mapPattern] using HasType.subst mappedBody mappedReplacement
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have mappedElements := elementsTyped.mapRows symbols rows
        simpa [mapPattern, mapTypeExpr] using
          (HasType.collection (rest := rest) mappedElements)
    | @collectionConstructor bound rule parameterName collectionType elements rest
        elementType supported membership parameterShape elementsTyped =>
        obtain ⟨targetRule, targetMembership, targetLabel, targetCategory,
          targetParameters⟩ := rows rule membership supported
        have mappedElements := elementsTyped.mapRows symbols rows
        have mappedParameterShape :
            targetRule.params =
              [.simple parameterName
                (.collection collectionType
                  (mapTypeExpr symbols elementType))] := by
          simp [targetParameters, parameterShape, mapTermParam, mapTypeExpr]
        simpa [mapPattern, targetLabel, targetCategory, mapTypeExpr] using
          (HasType.collectionConstructor
            targetMembership mappedParameterShape
            mappedElements)

  /-- Supported row witnesses preserve ordered argument typing. -/
  theorem ArgumentsHaveTypesWithConstructors.mapRows
      {source target : LanguageDef} {allowed : String → Prop}
      (symbols : LanguageDefSymbolMap)
      (rows : ∀ rule ∈ source.terms, allowed rule.label →
        ∃ targetRule ∈ target.terms,
          targetRule.label = symbols.constructor rule.label ∧
          targetRule.category = symbols.sort rule.category ∧
          targetRule.params = rule.params.map (mapTermParam symbols))
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypesWithConstructors source allowed free bound
        arguments parameters) :
      ArgumentsHaveTypes target (free.map symbols)
        (bound.map (mapTypeExpr symbols))
        (arguments.map (mapPattern symbols))
        (parameters.map (mapTermParam symbols)) := by
    cases typed with
    | nil => exact .nil
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        have mappedParameterType :
            parameterType? (mapTermParam symbols parameter) =
              some (mapTypeExpr symbols expected) := by
          rw [parameterType?_mapTermParam, parameterType]
          rfl
        apply ArgumentsHaveTypes.cons
        · exact (matchesParameterRepresentation_map_iff
            symbols parameter argument).2 representation
        · exact mappedParameterType
        · exact argumentTyped.mapRows symbols rows
        · exact argumentsTyped.mapRows symbols rows

  /-- Supported row witnesses preserve collection-element typing. -/
  theorem ElementsHaveTypeWithConstructors.mapRows
      {source target : LanguageDef} {allowed : String → Prop}
      (symbols : LanguageDefSymbolMap)
      (rows : ∀ rule ∈ source.terms, allowed rule.label →
        ∃ targetRule ∈ target.terms,
          targetRule.label = symbols.constructor rule.label ∧
          targetRule.category = symbols.sort rule.category ∧
          targetRule.params = rule.params.map (mapTermParam symbols))
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveTypeWithConstructors source allowed free bound
        elements elementType) :
      ElementsHaveType target (free.map symbols)
        (bound.map (mapTypeExpr symbols))
        (elements.map (mapPattern symbols))
        (mapTypeExpr symbols elementType) := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons (elementTyped.mapRows symbols rows)
          (elementsTyped.mapRows symbols rows)
end


end WellSorted
end Mettapedia.GSLT.LanguageDef
