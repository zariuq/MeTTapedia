import Mettapedia.GSLT.LanguageDef.RestAwareTyping

/-!
# Transport of rest-aware schemas along typed presentation maps

The same typed-profile morphism used by ordinary authored typing also
transports schema typing. A collection rest retains its name and collection
kind, while its declared element type follows the sort action. No injectivity
of constructor or sort symbols is needed for the forward typing direction.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

/-- The exact collection type required by a rest moves with the free typing
context and element type. -/
theorem RestHasType.map
    {free : FreeTypeContext} {kind : CollType}
    {elementType : TypeExpr} {rest : Option String}
    (symbols : LanguageDefSymbolMap)
    (typed : RestHasType free kind elementType rest) :
    RestHasType (free.map symbols) kind
      (mapTypeExpr symbols elementType) rest := by
  cases rest with
  | none => trivial
  | some name =>
      simpa [RestHasType, FreeTypeContext.map, mapTypeExpr] using
        congrArg (Option.map (mapTypeExpr symbols)) typed

mutual
  /-- Typed-profile maps preserve all of a schema's typing premises,
  including rests at arbitrary depth. -/
  theorem HasType.mapTyping
      {source target : ValidatedLanguageDef}
      (morphism : TypingMorphism source target)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : HasType source.language free bound pattern type) :
      HasType target.language (free.map morphism.symbols)
        (bound.map (mapTypeExpr morphism.symbols))
        (mapPattern morphism.symbols pattern)
        (mapTypeExpr morphism.symbols type) := by
    cases typed with
    | @bvar bound index type lookup =>
        have mappedLookup :
            (bound.map (mapTypeExpr morphism.symbols))[index]? =
              some (mapTypeExpr morphism.symbols type) := by
          simpa using congrArg
            (Option.map (mapTypeExpr morphism.symbols)) lookup
        simpa [mapPattern] using
          (HasType.bvar (free := free.map morphism.symbols) mappedLookup)
    | @fvar bound name type lookup =>
        have mappedLookup :
            (free.map morphism.symbols) name =
              some (mapTypeExpr morphism.symbols type) := by
          simp [FreeTypeContext.map, lookup]
        simpa [mapPattern] using
          (HasType.fvar
            (bound := bound.map (mapTypeExpr morphism.symbols)) mappedLookup)
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        obtain ⟨targetRule, targetMembership, targetLabel, targetCategory,
          targetParameters⟩ := morphism.mapsTerms rule membership
        have mappedArguments := argumentsTyped.mapTyping morphism
        have mappedNotBare :
            ¬ UsesBareCollection (mapGrammarRule morphism.symbols rule) :=
          fun mappedBare => notBare
            ((usesBareCollection_mapGrammarRule_iff morphism.symbols rule).mp
              mappedBare)
        have targetArguments :
            ArgumentsHaveTypes target.language
              (free.map morphism.symbols)
              (bound.map (mapTypeExpr morphism.symbols))
              (arguments.map (mapPattern morphism.symbols))
              targetRule.params := by
          simpa [targetParameters] using mappedArguments
        simpa [mapPattern, targetLabel, targetCategory, mapTypeExpr] using
          (HasType.constructor targetMembership (by
            simpa [UsesBareCollection, targetParameters, mapGrammarRule] using
              mappedNotBare) targetArguments)
    | @lambda bound binder body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapTyping morphism
        simpa [mapPattern, mapTypeExpr] using HasType.lambda mappedBody
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapTyping morphism
        have mappedBody' :
            HasType target.language (free.map morphism.symbols)
              (List.replicate arity (mapTypeExpr morphism.symbols domain) ++
                bound.map (mapTypeExpr morphism.symbols))
              (mapPattern morphism.symbols body)
              (mapTypeExpr morphism.symbols codomain) := by
          simpa [List.map_append, List.map_replicate] using mappedBody
        simpa [mapPattern, mapTypeExpr] using
          HasType.multiLambda mappedBody'
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        have mappedBody := bodyTyped.mapTyping morphism
        have mappedReplacement := replacementTyped.mapTyping morphism
        simpa [mapPattern] using
          HasType.subst mappedBody mappedReplacement
    | @collection bound kind elements rest elementType elementsTyped restTyped =>
        have mappedElements := elementsTyped.mapTyping morphism
        simpa [mapPattern, mapTypeExpr] using
          (HasType.collection (rest := rest) mappedElements
            (restTyped.map morphism.symbols))
    | @collectionConstructor bound rule parameterName kind elements rest
        elementType membership parameterShape elementsTyped restTyped =>
        obtain ⟨targetRule, targetMembership, targetLabel, targetCategory,
          targetParameters⟩ := morphism.mapsTerms rule membership
        have mappedElements := elementsTyped.mapTyping morphism
        have mappedParameterShape :
            targetRule.params =
              [.simple parameterName
                (.collection kind
                  (mapTypeExpr morphism.symbols elementType))] := by
          simp [targetParameters, parameterShape, mapTermParam, mapTypeExpr]
        simpa [mapPattern, targetLabel, targetCategory, mapTypeExpr] using
          (HasType.collectionConstructor targetMembership
            mappedParameterShape mappedElements
            (restTyped.map morphism.symbols))

  theorem ArgumentsHaveTypes.mapTyping
      {source target : ValidatedLanguageDef}
      (morphism : TypingMorphism source target)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes source.language free bound
        arguments parameters) :
      ArgumentsHaveTypes target.language (free.map morphism.symbols)
        (bound.map (mapTypeExpr morphism.symbols))
        (arguments.map (mapPattern morphism.symbols))
        (parameters.map (mapTermParam morphism.symbols)) := by
    cases typed with
    | nil => exact .nil
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        have mappedParameterType :
            parameterType? (mapTermParam morphism.symbols parameter) =
              some (mapTypeExpr morphism.symbols expected) := by
          rw [parameterType?_mapTermParam, parameterType]
          rfl
        apply ArgumentsHaveTypes.cons
        · exact (matchesParameterRepresentation_map_iff
            morphism.symbols parameter argument).2 representation
        · exact mappedParameterType
        · exact argumentTyped.mapTyping morphism
        · exact argumentsTyped.mapTyping morphism

  theorem ElementsHaveType.mapTyping
      {source target : ValidatedLanguageDef}
      (morphism : TypingMorphism source target)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType source.language free bound
        elements elementType) :
      ElementsHaveType target.language (free.map morphism.symbols)
        (bound.map (mapTypeExpr morphism.symbols))
        (elements.map (mapPattern morphism.symbols))
        (mapTypeExpr morphism.symbols elementType) := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons (elementTyped.mapTyping morphism)
          (elementsTyped.mapTyping morphism)
end

theorem HasType.map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasType source.language free bound pattern type) :
    HasType target.language (free.map morphism.symbols)
      (bound.map (mapTypeExpr morphism.symbols))
      (mapPattern morphism.symbols pattern)
      (mapTypeExpr morphism.symbols type) :=
  typed.mapTyping morphism.toTyping

/-- A mapped schema pair retains its common type and every rest declaration
under the authored type-context action. The weakest typed-profile map suffices. -/
theorem SchemaSidesHaveType.mapTyping
    {source target : ValidatedLanguageDef}
    (morphism : TypingMorphism source target)
    {typeContext : List (String × TypeExpr)} {left right : Pattern}
    (typed : SchemaSidesHaveType source.language typeContext left right) :
    SchemaSidesHaveType target.language
      (mapTypeContext morphism.symbols typeContext)
      (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) := by
  obtain ⟨type, leftTyped, rightTyped⟩ := typed
  refine ⟨mapTypeExpr morphism.symbols type, ?_, ?_⟩
  · simpa [FreeTypeContext.ofList_mapTypeContext] using
      leftTyped.mapTyping morphism
  · simpa [FreeTypeContext.ofList_mapTypeContext] using
      rightTyped.mapTyping morphism

theorem SchemaSidesHaveType.map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {typeContext : List (String × TypeExpr)} {left right : Pattern}
    (typed : SchemaSidesHaveType source.language typeContext left right) :
    SchemaSidesHaveType target.language
      (mapTypeContext morphism.symbols typeContext)
      (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) :=
  typed.mapTyping morphism.toTyping

theorem RewriteHasType.map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {rewrite : RewriteRule}
    (typed : RewriteHasType source.language rewrite) :
    RewriteHasType target.language
      (mapRewriteRule morphism.symbols rewrite) := by
  exact SchemaSidesHaveType.map morphism typed

theorem EquationHasType.map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {equation : Equation}
    (typed : EquationHasType source.language equation) :
    EquationHasType target.language
      (mapEquation morphism.symbols equation) := by
  exact SchemaSidesHaveType.map morphism typed

/-- A structural map sends every typed source rewrite to a typed rewrite in
the target. It does not type additional target rewrites. -/
theorem RewritesHaveType.map_image
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typed : RewritesHaveType source)
    {rewrite : RewriteRule} (membership : rewrite ∈ source.language.rewrites) :
    RewriteHasType target.language
      (mapRewriteRule morphism.symbols rewrite) :=
  (typed rewrite membership).map morphism

/-- All target rewrites inherit typing when the structural map covers the
entire target rewrite list. The coverage premise is essential for extensions. -/
theorem RewritesHaveType.map_of_surjective
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typed : RewritesHaveType source)
    (covers : ∀ rewrite ∈ target.language.rewrites,
      ∃ sourceRewrite ∈ source.language.rewrites,
        mapRewriteRule morphism.symbols sourceRewrite = rewrite) :
    RewritesHaveType target := by
  intro rewrite membership
  obtain ⟨sourceRewrite, sourceMembership, equality⟩ :=
    covers rewrite membership
  subst rewrite
  exact typed.map_image morphism sourceMembership

theorem EquationsHaveType.map_image
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typed : EquationsHaveType source)
    {equation : Equation} (membership : equation ∈ source.language.equations) :
    EquationHasType target.language
      (mapEquation morphism.symbols equation) :=
  (typed equation membership).map morphism

theorem EquationsHaveType.map_of_surjective
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typed : EquationsHaveType source)
    (covers : ∀ equation ∈ target.language.equations,
      ∃ sourceEquation ∈ source.language.equations,
        mapEquation morphism.symbols sourceEquation = equation) :
    EquationsHaveType target := by
  intro equation membership
  obtain ⟨sourceEquation, sourceMembership, equality⟩ :=
    covers equation membership
  subst equation
  exact typed.map_image morphism sourceMembership

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
