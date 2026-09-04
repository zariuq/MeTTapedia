import Mettapedia.GSLT.LanguageDef.StructuralCoproduct
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Exact typing fibres of structural presentation coproducts

Operational noninterference is not enough for a typed language sum.  This
module proves that the executable, declaration-derived typing checker sees
exactly the original typing fibre on either component image.  Combined with
the checker's soundness and completeness theorem, this gives reflection as
well as preservation for object-term typing.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuralCoproductTyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralCoproduct
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem beq_map_eq
    {carrier target : Type} [BEq carrier] [LawfulBEq carrier]
    [BEq target] [LawfulBEq target]
    (map : carrier → target) (injective : Function.Injective map)
    (first second : carrier) :
    (map first == map second) = (first == second) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact injective.eq_iff

private theorem getElem?_map_eq_some_iff
    {carrier target : Type} (map : carrier → target)
    (injective : Function.Injective map) (elements : List carrier)
    (index : Nat) (expected : carrier) :
    (elements.map map)[index]? = some (map expected) ↔
      elements[index]? = some expected := by
  rw [List.getElem?_map]
  cases lookup : elements[index]? with
  | none => simp
  | some actual => simp [injective.eq_iff]

private theorem free_map_eq_some_iff
    (symbols : LanguageDefSymbolMap)
    (sortInjective : Function.Injective symbols.sort)
    (free : FreeTypeContext) (name : String) (expected : TypeExpr) :
    free.map symbols name = some (mapTypeExpr symbols expected) ↔
      free name = some expected := by
  unfold FreeTypeContext.map
  cases lookup : free name with
  | none => simp
  | some actual =>
      simp [(mapTypeExpr_injective symbols sortInjective).eq_iff]

private theorem matchesParameterRepresentation?_map
    (symbols : LanguageDefSymbolMap) (parameter : TermParam)
    (argument : Pattern) :
    matchesParameterRepresentation? (mapTermParam symbols parameter)
        (mapPattern symbols argument) =
      matchesParameterRepresentation? parameter argument := by
  cases parameter with
  | simple name type =>
      cases argument <;>
        simp [matchesParameterRepresentation?, mapTermParam, mapPattern]
  | abstractionNamed binderName bodyName type =>
      cases argument <;>
        simp [matchesParameterRepresentation?, mapTermParam, mapPattern]
      case lambda binder body => cases binder <;> rfl
  | multiAbstractionNamed binderNames bodyName type =>
      cases argument <;>
        simp [matchesParameterRepresentation?, mapTermParam, mapPattern]
      case multiLambda arity binders body => cases binders <;> rfl

private theorem usesBareCollection?_map
    (symbols : LanguageDefSymbolMap) (rule : GrammarRule) :
    usesBareCollection? (mapGrammarRule symbols rule) =
      usesBareCollection? rule := by
  cases rule with
  | mk label category parameters syntaxPattern evalPolicy =>
      cases parameters with
      | nil => rfl
      | cons parameter remaining =>
          cases remaining with
          | nil =>
              cases parameter with
              | simple name type =>
                  cases type <;>
                    simp [usesBareCollection?, mapGrammarRule, mapTermParam,
                      mapTypeExpr]
              | abstractionNamed binder body type =>
                  simp [usesBareCollection?, mapGrammarRule, mapTermParam]
              | multiAbstractionNamed binders body type =>
                  simp [usesBareCollection?, mapGrammarRule, mapTermParam]
          | cons next tail =>
              simp [usesBareCollection?, mapGrammarRule]

private def constructorCandidate
    (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (constructor : String)
    (arguments : List Pattern) (expected : TypeExpr)
    (rule : GrammarRule) : Bool :=
  rule.label == constructor &&
    expected == .base rule.category &&
    !usesBareCollection? rule &&
    checkArgumentsHaveTypes language free bound arguments rule.params

private def bareCollectionCandidate
    (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (collectionType : CollType)
    (elements : List Pattern) (expected : TypeExpr)
    (rule : GrammarRule) : Bool :=
  match bareCollectionElementType? rule collectionType expected with
  | some elementType =>
      checkElementsHaveType language free bound elements elementType
  | none => false

private theorem list_any_congr_of_mem {carrier : Type}
    (elements : List carrier) (first second : carrier → Bool)
    (agree : ∀ element ∈ elements, first element = second element) :
    elements.any first = elements.any second := by
  induction elements with
  | nil => rfl
  | cons element elements inductionHypothesis =>
      simp only [List.any_cons]
      rw [agree element (by simp)]
      rw [inductionHypothesis (fun other membership =>
        agree other (by simp [membership]))]

private theorem checkHasType_apply_eq_any
    (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (constructor : String)
    (arguments : List Pattern) (expected : TypeExpr) :
    checkHasType language free bound (.apply constructor arguments) expected =
      language.terms.any
        (constructorCandidate language free bound constructor arguments
          expected) := by
  rfl

private theorem checkArguments_map_exact
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (argumentExact : ∀ argument ∈ arguments, ∀ expected,
      checkHasType compatible.combinedLanguage.language (free.map leftSymbols)
          (bound.map (mapTypeExpr leftSymbols))
          (mapPattern leftSymbols argument) (mapTypeExpr leftSymbols expected) =
        checkHasType left.language free bound argument expected) :
    checkArgumentsHaveTypes compatible.combinedLanguage.language
        (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
        (arguments.map (mapPattern leftSymbols))
        (parameters.map (mapTermParam leftSymbols)) =
      checkArgumentsHaveTypes left.language free bound arguments parameters := by
  induction arguments generalizing parameters with
  | nil => cases parameters <;> rfl
  | cons argument arguments inductionHypothesis =>
      cases parameters with
      | nil => rfl
      | cons parameter parameters =>
          cases parameterTypeEquation : parameterType? parameter with
          | none =>
              simp [checkArgumentsHaveTypes, parameterType?_mapTermParam,
                parameterTypeEquation]
          | some expected =>
              simp only [List.map_cons, checkArgumentsHaveTypes,
                parameterType?_mapTermParam, parameterTypeEquation,
                Option.map_some]
              rw [matchesParameterRepresentation?_map]
              rw [argumentExact argument (by simp) expected]
              rw [inductionHypothesis (fun other membership otherExpected =>
                argumentExact other (by simp [membership]) otherExpected)]

private theorem checkElements_map_exact
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (elementExact : ∀ element ∈ elements,
      checkHasType compatible.combinedLanguage.language (free.map leftSymbols)
          (bound.map (mapTypeExpr leftSymbols))
          (mapPattern leftSymbols element)
          (mapTypeExpr leftSymbols elementType) =
        checkHasType left.language free bound element elementType) :
    checkElementsHaveType compatible.combinedLanguage.language
        (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
        (elements.map (mapPattern leftSymbols))
        (mapTypeExpr leftSymbols elementType) =
      checkElementsHaveType left.language free bound elements elementType := by
  induction elements with
  | nil => rfl
  | cons element elements inductionHypothesis =>
      simp only [List.map_cons, checkElementsHaveType]
      rw [elementExact element (by simp)]
      rw [inductionHypothesis (fun other membership =>
        elementExact other (by simp [membership]))]

private theorem constructorCandidate_left_map
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    (constructor : String) (arguments : List Pattern) (expected : TypeExpr)
    (rule : GrammarRule)
    (argumentsExact :
      checkArgumentsHaveTypes compatible.combinedLanguage.language
          (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
          (arguments.map (mapPattern leftSymbols))
          (rule.params.map (mapTermParam leftSymbols)) =
        checkArgumentsHaveTypes left.language free bound arguments rule.params) :
    constructorCandidate compatible.combinedLanguage.language
        (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
        (leftSymbols.constructor constructor)
        (arguments.map (mapPattern leftSymbols))
        (mapTypeExpr leftSymbols expected)
        (mapGrammarRule leftSymbols rule) =
      constructorCandidate left.language free bound constructor arguments
        expected rule := by
  unfold constructorCandidate
  simp only [mapGrammarRule]
  rw [beq_map_eq leftSymbols.constructor
    compatible.leftSymbolsInjective.constructor]
  have expectedCheck :
      (mapTypeExpr leftSymbols expected ==
          .base (leftSymbols.sort rule.category)) =
        (expected == .base rule.category) := by
    simpa [mapTypeExpr] using
      beq_map_eq (mapTypeExpr leftSymbols)
        (mapTypeExpr_injective leftSymbols
          compatible.leftSymbolsInjective.sort)
        expected (.base rule.category)
  rw [expectedCheck]
  have bareCheck := usesBareCollection?_map leftSymbols rule
  simp only [mapGrammarRule] at bareCheck
  rw [bareCheck, argumentsExact]

private theorem constructorCandidate_right_map_eq_false
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    (constructor : String) (arguments : List Pattern) (expected : TypeExpr)
    (rule : GrammarRule) :
    constructorCandidate compatible.combinedLanguage.language
        (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
        (leftSymbols.constructor constructor)
        (arguments.map (mapPattern leftSymbols))
        (mapTypeExpr leftSymbols expected)
        (mapGrammarRule rightSymbols rule) = false := by
  unfold constructorCandidate
  have unequal :
      rightSymbols.constructor rule.label ≠
        leftSymbols.constructor constructor :=
    fun equality => compatible.symbolImagesDisjoint.constructor
      constructor rule.label equality.symm
  simp [mapGrammarRule, unequal]

private theorem bareCollectionElementType?_left_map
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (rule : GrammarRule) (collectionType : CollType) (expected : TypeExpr) :
    bareCollectionElementType? (mapGrammarRule leftSymbols rule)
        collectionType (mapTypeExpr leftSymbols expected) =
      (bareCollectionElementType? rule collectionType expected).map
        (mapTypeExpr leftSymbols) := by
  cases rule with
  | mk label category parameters syntaxPattern evalPolicy =>
      cases expected <;> cases parameters with
      | nil => simp [bareCollectionElementType?, mapGrammarRule]
      | cons parameter parameters =>
          cases parameters with
          | cons next remaining =>
              simp [bareCollectionElementType?, mapGrammarRule]
          | nil =>
              cases parameter with
              | abstractionNamed binder body type =>
                  simp [bareCollectionElementType?, mapGrammarRule,
                    mapTermParam]
              | multiAbstractionNamed binders body type =>
                  simp [bareCollectionElementType?, mapGrammarRule,
                    mapTermParam]
              | simple parameterName parameterType =>
                  cases parameterType <;>
                    simp [bareCollectionElementType?, mapGrammarRule,
                      mapTermParam, mapTypeExpr,
                      compatible.leftSymbolsInjective.sort.eq_iff]

private theorem bareCollectionElementType?_right_map_eq_none
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (rule : GrammarRule) (collectionType : CollType) (expected : TypeExpr) :
    bareCollectionElementType? (mapGrammarRule rightSymbols rule)
        collectionType (mapTypeExpr leftSymbols expected) = none := by
  cases rule with
  | mk label category parameters syntaxPattern evalPolicy =>
      cases expected with
      | arrow domain codomain =>
          simp [bareCollectionElementType?, mapGrammarRule, mapTypeExpr]
      | multiBinder body =>
          simp [bareCollectionElementType?, mapGrammarRule, mapTypeExpr]
      | collection actual element =>
          simp [bareCollectionElementType?, mapGrammarRule, mapTypeExpr]
      | base expectedSort =>
          have unequal :
              rightSymbols.sort category ≠ leftSymbols.sort expectedSort :=
            fun equality => compatible.symbolImagesDisjoint.sort
              expectedSort category equality.symm
          cases parameters with
          | nil => simp [bareCollectionElementType?, mapGrammarRule]
          | cons parameter parameters =>
              cases parameters with
              | cons next remaining =>
                  simp [bareCollectionElementType?, mapGrammarRule]
              | nil =>
                  cases parameter with
                  | simple parameterName parameterType =>
                      cases parameterType <;>
                        simp [bareCollectionElementType?, mapGrammarRule,
                          mapTermParam, mapTypeExpr, unequal]
                  | abstractionNamed binder body type =>
                      simp [bareCollectionElementType?, mapGrammarRule,
                        mapTermParam, mapTypeExpr]
                  | multiAbstractionNamed binders body type =>
                      simp [bareCollectionElementType?, mapGrammarRule,
                        mapTermParam, mapTypeExpr]

private theorem bareCollectionCandidate_left_map
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    (collectionType : CollType) (elements : List Pattern)
    (expected : TypeExpr) (rule : GrammarRule)
    (elementsExact : ∀ elementType,
      checkElementsHaveType compatible.combinedLanguage.language
          (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
          (elements.map (mapPattern leftSymbols))
          (mapTypeExpr leftSymbols elementType) =
        checkElementsHaveType left.language free bound elements elementType) :
    bareCollectionCandidate compatible.combinedLanguage.language
        (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
        collectionType (elements.map (mapPattern leftSymbols))
        (mapTypeExpr leftSymbols expected) (mapGrammarRule leftSymbols rule) =
      bareCollectionCandidate left.language free bound collectionType elements
        expected rule := by
  unfold bareCollectionCandidate
  rw [bareCollectionElementType?_left_map compatible]
  cases bareCollectionElementType? rule collectionType expected with
  | none => rfl
  | some elementType => exact elementsExact elementType

private theorem bareCollectionCandidate_right_map_eq_false
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    (collectionType : CollType) (elements : List Pattern)
    (expected : TypeExpr) (rule : GrammarRule) :
    bareCollectionCandidate compatible.combinedLanguage.language
        (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
        collectionType (elements.map (mapPattern leftSymbols))
        (mapTypeExpr leftSymbols expected) (mapGrammarRule rightSymbols rule) =
      false := by
  unfold bareCollectionCandidate
  rw [bareCollectionElementType?_right_map_eq_none compatible]

private theorem directCollection_map_exact
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    (collectionType : CollType) (elements : List Pattern)
    (expected : TypeExpr)
    (elementsExact : ∀ elementType,
      checkElementsHaveType compatible.combinedLanguage.language
          (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
          (elements.map (mapPattern leftSymbols))
          (mapTypeExpr leftSymbols elementType) =
        checkElementsHaveType left.language free bound elements elementType) :
    (match mapTypeExpr leftSymbols expected with
    | .collection actual elementType =>
        actual == collectionType &&
          checkElementsHaveType compatible.combinedLanguage.language
            (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
            (elements.map (mapPattern leftSymbols)) elementType
    | _ => false) =
    (match expected with
    | .collection actual elementType =>
        actual == collectionType &&
          checkElementsHaveType left.language free bound elements elementType
    | _ => false) := by
  cases expected <;> simp [mapTypeExpr, elementsExact]

private theorem checkArguments_right_map_exact
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (argumentExact : ∀ argument ∈ arguments, ∀ expected,
      checkHasType compatible.combinedLanguage.language (free.map rightSymbols)
          (bound.map (mapTypeExpr rightSymbols))
          (mapPattern rightSymbols argument) (mapTypeExpr rightSymbols expected) =
        checkHasType right.language free bound argument expected) :
    checkArgumentsHaveTypes compatible.combinedLanguage.language
        (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
        (arguments.map (mapPattern rightSymbols))
        (parameters.map (mapTermParam rightSymbols)) =
      checkArgumentsHaveTypes right.language free bound arguments parameters := by
  induction arguments generalizing parameters with
  | nil => cases parameters <;> rfl
  | cons argument arguments inductionHypothesis =>
      cases parameters with
      | nil => rfl
      | cons parameter parameters =>
          cases parameterTypeEquation : parameterType? parameter with
          | none =>
              simp [checkArgumentsHaveTypes, parameterType?_mapTermParam,
                parameterTypeEquation]
          | some expected =>
              simp only [List.map_cons, checkArgumentsHaveTypes,
                parameterType?_mapTermParam, parameterTypeEquation,
                Option.map_some]
              rw [matchesParameterRepresentation?_map]
              rw [argumentExact argument (by simp) expected]
              rw [inductionHypothesis (fun other membership otherExpected =>
                argumentExact other (by simp [membership]) otherExpected)]

private theorem checkElements_right_map_exact
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (elementExact : ∀ element ∈ elements,
      checkHasType compatible.combinedLanguage.language (free.map rightSymbols)
          (bound.map (mapTypeExpr rightSymbols))
          (mapPattern rightSymbols element)
          (mapTypeExpr rightSymbols elementType) =
        checkHasType right.language free bound element elementType) :
    checkElementsHaveType compatible.combinedLanguage.language
        (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
        (elements.map (mapPattern rightSymbols))
        (mapTypeExpr rightSymbols elementType) =
      checkElementsHaveType right.language free bound elements elementType := by
  induction elements with
  | nil => rfl
  | cons element elements inductionHypothesis =>
      simp only [List.map_cons, checkElementsHaveType]
      rw [elementExact element (by simp)]
      rw [inductionHypothesis (fun other membership =>
        elementExact other (by simp [membership]))]

private theorem constructorCandidate_right_source_map
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    (constructor : String) (arguments : List Pattern) (expected : TypeExpr)
    (rule : GrammarRule)
    (argumentsExact :
      checkArgumentsHaveTypes compatible.combinedLanguage.language
          (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
          (arguments.map (mapPattern rightSymbols))
          (rule.params.map (mapTermParam rightSymbols)) =
        checkArgumentsHaveTypes right.language free bound arguments rule.params) :
    constructorCandidate compatible.combinedLanguage.language
        (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
        (rightSymbols.constructor constructor)
        (arguments.map (mapPattern rightSymbols))
        (mapTypeExpr rightSymbols expected)
        (mapGrammarRule rightSymbols rule) =
      constructorCandidate right.language free bound constructor arguments
        expected rule := by
  unfold constructorCandidate
  simp only [mapGrammarRule]
  rw [beq_map_eq rightSymbols.constructor
    compatible.rightSymbolsInjective.constructor]
  have expectedCheck :
      (mapTypeExpr rightSymbols expected ==
          .base (rightSymbols.sort rule.category)) =
        (expected == .base rule.category) := by
    simpa [mapTypeExpr] using
      beq_map_eq (mapTypeExpr rightSymbols)
        (mapTypeExpr_injective rightSymbols
          compatible.rightSymbolsInjective.sort)
        expected (.base rule.category)
  rw [expectedCheck]
  have bareCheck := usesBareCollection?_map rightSymbols rule
  simp only [mapGrammarRule] at bareCheck
  rw [bareCheck, argumentsExact]

private theorem constructorCandidate_left_map_eq_false_on_right
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    (constructor : String) (arguments : List Pattern) (expected : TypeExpr)
    (rule : GrammarRule) :
    constructorCandidate compatible.combinedLanguage.language
        (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
        (rightSymbols.constructor constructor)
        (arguments.map (mapPattern rightSymbols))
        (mapTypeExpr rightSymbols expected)
        (mapGrammarRule leftSymbols rule) = false := by
  unfold constructorCandidate
  have unequal :
      leftSymbols.constructor rule.label ≠
        rightSymbols.constructor constructor :=
    compatible.symbolImagesDisjoint.constructor rule.label constructor
  simp [mapGrammarRule, unequal]

private theorem bareCollectionElementType?_right_source_map
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (rule : GrammarRule) (collectionType : CollType) (expected : TypeExpr) :
    bareCollectionElementType? (mapGrammarRule rightSymbols rule)
        collectionType (mapTypeExpr rightSymbols expected) =
      (bareCollectionElementType? rule collectionType expected).map
        (mapTypeExpr rightSymbols) := by
  cases rule with
  | mk label category parameters syntaxPattern evalPolicy =>
      cases expected <;> cases parameters with
      | nil => simp [bareCollectionElementType?, mapGrammarRule]
      | cons parameter parameters =>
          cases parameters with
          | cons next remaining =>
              simp [bareCollectionElementType?, mapGrammarRule]
          | nil =>
              cases parameter with
              | abstractionNamed binder body type =>
                  simp [bareCollectionElementType?, mapGrammarRule,
                    mapTermParam]
              | multiAbstractionNamed binders body type =>
                  simp [bareCollectionElementType?, mapGrammarRule,
                    mapTermParam]
              | simple parameterName parameterType =>
                  cases parameterType <;>
                    simp [bareCollectionElementType?, mapGrammarRule,
                      mapTermParam, mapTypeExpr,
                      compatible.rightSymbolsInjective.sort.eq_iff]

private theorem bareCollectionElementType?_left_map_eq_none_on_right
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (rule : GrammarRule) (collectionType : CollType) (expected : TypeExpr) :
    bareCollectionElementType? (mapGrammarRule leftSymbols rule)
        collectionType (mapTypeExpr rightSymbols expected) = none := by
  cases rule with
  | mk label category parameters syntaxPattern evalPolicy =>
      cases expected with
      | arrow domain codomain =>
          simp [bareCollectionElementType?, mapGrammarRule, mapTypeExpr]
      | multiBinder body =>
          simp [bareCollectionElementType?, mapGrammarRule, mapTypeExpr]
      | collection actual element =>
          simp [bareCollectionElementType?, mapGrammarRule, mapTypeExpr]
      | base expectedSort =>
          have unequal :
              leftSymbols.sort category ≠ rightSymbols.sort expectedSort :=
            compatible.symbolImagesDisjoint.sort category expectedSort
          cases parameters with
          | nil => simp [bareCollectionElementType?, mapGrammarRule]
          | cons parameter parameters =>
              cases parameters with
              | cons next remaining =>
                  simp [bareCollectionElementType?, mapGrammarRule]
              | nil =>
                  cases parameter with
                  | simple parameterName parameterType =>
                      cases parameterType <;>
                        simp [bareCollectionElementType?, mapGrammarRule,
                          mapTermParam, mapTypeExpr, unequal]
                  | abstractionNamed binder body type =>
                      simp [bareCollectionElementType?, mapGrammarRule,
                        mapTermParam, mapTypeExpr]
                  | multiAbstractionNamed binders body type =>
                      simp [bareCollectionElementType?, mapGrammarRule,
                        mapTermParam, mapTypeExpr]

private theorem bareCollectionCandidate_right_source_map
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    (collectionType : CollType) (elements : List Pattern)
    (expected : TypeExpr) (rule : GrammarRule)
    (elementsExact : ∀ elementType,
      checkElementsHaveType compatible.combinedLanguage.language
          (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
          (elements.map (mapPattern rightSymbols))
          (mapTypeExpr rightSymbols elementType) =
        checkElementsHaveType right.language free bound elements elementType) :
    bareCollectionCandidate compatible.combinedLanguage.language
        (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
        collectionType (elements.map (mapPattern rightSymbols))
        (mapTypeExpr rightSymbols expected) (mapGrammarRule rightSymbols rule) =
      bareCollectionCandidate right.language free bound collectionType elements
        expected rule := by
  unfold bareCollectionCandidate
  rw [bareCollectionElementType?_right_source_map compatible]
  cases bareCollectionElementType? rule collectionType expected with
  | none => rfl
  | some elementType => exact elementsExact elementType

private theorem bareCollectionCandidate_left_map_eq_false_on_right
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    (collectionType : CollType) (elements : List Pattern)
    (expected : TypeExpr) (rule : GrammarRule) :
    bareCollectionCandidate compatible.combinedLanguage.language
        (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
        collectionType (elements.map (mapPattern rightSymbols))
        (mapTypeExpr rightSymbols expected) (mapGrammarRule leftSymbols rule) =
      false := by
  unfold bareCollectionCandidate
  rw [bareCollectionElementType?_left_map_eq_none_on_right compatible]

private theorem directCollection_right_map_exact
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    (collectionType : CollType) (elements : List Pattern)
    (expected : TypeExpr)
    (elementsExact : ∀ elementType,
      checkElementsHaveType compatible.combinedLanguage.language
          (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
          (elements.map (mapPattern rightSymbols))
          (mapTypeExpr rightSymbols elementType) =
        checkElementsHaveType right.language free bound elements elementType) :
    (match mapTypeExpr rightSymbols expected with
    | .collection actual elementType =>
        actual == collectionType &&
          checkElementsHaveType compatible.combinedLanguage.language
            (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
            (elements.map (mapPattern rightSymbols)) elementType
    | _ => false) =
    (match expected with
    | .collection actual elementType =>
        actual == collectionType &&
          checkElementsHaveType right.language free bound elements elementType
    | _ => false) := by
  cases expected <;> simp [mapTypeExpr, elementsExact]

/-- Exact executable typing on the image of the left component.  The equality
is at the Boolean decision boundary, so it entails both preservation and
reflection without introducing a second typing relation. -/
theorem left_checkHasType_exact
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (pattern : Pattern) (expected : TypeExpr) :
    checkHasType compatible.combinedLanguage.language (free.map leftSymbols)
        (bound.map (mapTypeExpr leftSymbols))
        (mapPattern leftSymbols pattern) (mapTypeExpr leftSymbols expected) =
      checkHasType left.language free bound pattern expected := by
  induction pattern using Pattern.inductionOn generalizing bound expected with
  | hbvar index =>
      simp only [mapPattern, checkHasType]
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact getElem?_map_eq_some_iff (mapTypeExpr leftSymbols)
        (mapTypeExpr_injective leftSymbols
          compatible.leftSymbolsInjective.sort) bound index expected
  | hfvar freeName =>
      simp only [mapPattern, checkHasType]
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact free_map_eq_some_iff leftSymbols
        compatible.leftSymbolsInjective.sort free freeName expected
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map]
      rw [checkHasType_apply_eq_any, checkHasType_apply_eq_any]
      have leftAny :
          (left.language.terms.map (mapGrammarRule leftSymbols)).any
              (constructorCandidate compatible.combinedLanguage.language
                (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
                (leftSymbols.constructor constructor)
                (arguments.map (mapPattern leftSymbols))
                (mapTypeExpr leftSymbols expected)) =
            left.language.terms.any
              (constructorCandidate left.language free bound constructor
                arguments expected) := by
        rw [List.any_map]
        apply list_any_congr_of_mem
        intro rule membership
        exact constructorCandidate_left_map compatible constructor arguments
          expected rule
          (checkArguments_map_exact compatible
            (fun argument argumentMember argumentExpected =>
              inductionHypothesis argument argumentMember bound
                argumentExpected))
      have rightAny :
          (right.language.terms.map (mapGrammarRule rightSymbols)).any
              (constructorCandidate compatible.combinedLanguage.language
                (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
                (leftSymbols.constructor constructor)
                (arguments.map (mapPattern leftSymbols))
                (mapTypeExpr leftSymbols expected)) = false := by
        rw [List.any_map, List.any_eq_false]
        intro rule membership
        simp only [Function.comp_apply]
        rw [constructorCandidate_right_map_eq_false compatible constructor
          arguments expected rule]
        exact Bool.false_ne_true
      rw [show compatible.combinedLanguage.language.terms =
        left.language.terms.map (mapGrammarRule leftSymbols) ++
          right.language.terms.map (mapGrammarRule rightSymbols) by rfl]
      rw [List.any_append]
      rw [leftAny, rightAny, Bool.or_false]
  | hlambda binder body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          simpa [mapPattern, mapTypeExpr, checkHasType] using
            inductionHypothesis (domain :: bound) codomain
      | base sort => simp [mapPattern, mapTypeExpr, checkHasType]
      | multiBinder body => simp [mapPattern, mapTypeExpr, checkHasType]
      | collection collectionType element =>
          simp [mapPattern, mapTypeExpr, checkHasType]
  | hmultiLambda arity binders body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder binderType =>
              simpa [mapPattern, mapTypeExpr, checkHasType, List.map_append,
                List.map_replicate] using
                inductionHypothesis
                  (List.replicate arity binderType ++ bound) codomain
          | base sort => simp [mapPattern, mapTypeExpr, checkHasType]
          | arrow first second => simp [mapPattern, mapTypeExpr, checkHasType]
          | collection collectionType element =>
              simp [mapPattern, mapTypeExpr, checkHasType]
      | base sort => simp [mapPattern, mapTypeExpr, checkHasType]
      | multiBinder body => simp [mapPattern, mapTypeExpr, checkHasType]
      | collection collectionType element =>
          simp [mapPattern, mapTypeExpr, checkHasType]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      rfl
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsExact : ∀ elementType,
          checkElementsHaveType compatible.combinedLanguage.language
              (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
              (elements.map (mapPattern leftSymbols))
              (mapTypeExpr leftSymbols elementType) =
            checkElementsHaveType left.language free bound elements
              elementType := fun elementType =>
        checkElements_map_exact compatible
          (fun element elementMember =>
            inductionHypothesis element elementMember bound elementType)
      have leftAny :
          (left.language.terms.map (mapGrammarRule leftSymbols)).any
              (bareCollectionCandidate compatible.combinedLanguage.language
                (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
                collectionType (elements.map (mapPattern leftSymbols))
                (mapTypeExpr leftSymbols expected)) =
            left.language.terms.any
              (bareCollectionCandidate left.language free bound
                collectionType elements expected) := by
        rw [List.any_map]
        apply list_any_congr_of_mem
        intro rule membership
        exact bareCollectionCandidate_left_map compatible collectionType
          elements expected rule elementsExact
      have rightAny :
          (right.language.terms.map (mapGrammarRule rightSymbols)).any
              (bareCollectionCandidate compatible.combinedLanguage.language
                (free.map leftSymbols) (bound.map (mapTypeExpr leftSymbols))
                collectionType (elements.map (mapPattern leftSymbols))
                (mapTypeExpr leftSymbols expected)) = false := by
        rw [List.any_map, List.any_eq_false]
        intro rule membership
        simp only [Function.comp_apply]
        rw [bareCollectionCandidate_right_map_eq_false compatible
          collectionType elements expected rule]
        exact Bool.false_ne_true
      have directExact := directCollection_map_exact compatible
        collectionType elements expected elementsExact
      have authoredExact :
          ((left.language.terms.map (mapGrammarRule leftSymbols)).any
              (bareCollectionCandidate compatible.combinedLanguage.language
                (free.map leftSymbols)
                (bound.map (mapTypeExpr leftSymbols)) collectionType
                (elements.map (mapPattern leftSymbols))
                (mapTypeExpr leftSymbols expected)) ||
            (right.language.terms.map (mapGrammarRule rightSymbols)).any
              (bareCollectionCandidate compatible.combinedLanguage.language
                (free.map leftSymbols)
                (bound.map (mapTypeExpr leftSymbols)) collectionType
                (elements.map (mapPattern leftSymbols))
                (mapTypeExpr leftSymbols expected))) =
            left.language.terms.any
              (bareCollectionCandidate left.language free bound collectionType
                elements expected) := by
        rw [leftAny, rightAny, Bool.or_false]
      simp only [mapPattern, mapPatternList_eq_map, checkHasType]
      rw [show compatible.combinedLanguage.language.terms =
        left.language.terms.map (mapGrammarRule leftSymbols) ++
          right.language.terms.map (mapGrammarRule rightSymbols) by rfl]
      rw [List.any_append]
      apply congrArg (fun value : Bool => rest.isNone && value)
      apply congrArg₂ (fun first second : Bool => first || second)
      · exact directExact
      · exact authoredExact

/-- Exact executable typing on the image of the right component. -/
theorem right_checkHasType_exact
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (pattern : Pattern) (expected : TypeExpr) :
    checkHasType compatible.combinedLanguage.language (free.map rightSymbols)
        (bound.map (mapTypeExpr rightSymbols))
        (mapPattern rightSymbols pattern) (mapTypeExpr rightSymbols expected) =
      checkHasType right.language free bound pattern expected := by
  induction pattern using Pattern.inductionOn generalizing bound expected with
  | hbvar index =>
      simp only [mapPattern, checkHasType]
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact getElem?_map_eq_some_iff (mapTypeExpr rightSymbols)
        (mapTypeExpr_injective rightSymbols
          compatible.rightSymbolsInjective.sort) bound index expected
  | hfvar freeName =>
      simp only [mapPattern, checkHasType]
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact free_map_eq_some_iff rightSymbols
        compatible.rightSymbolsInjective.sort free freeName expected
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map]
      rw [checkHasType_apply_eq_any, checkHasType_apply_eq_any]
      have leftAny :
          (left.language.terms.map (mapGrammarRule leftSymbols)).any
              (constructorCandidate compatible.combinedLanguage.language
                (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
                (rightSymbols.constructor constructor)
                (arguments.map (mapPattern rightSymbols))
                (mapTypeExpr rightSymbols expected)) = false := by
        rw [List.any_map, List.any_eq_false]
        intro rule membership
        simp only [Function.comp_apply]
        rw [constructorCandidate_left_map_eq_false_on_right compatible
          constructor arguments expected rule]
        exact Bool.false_ne_true
      have rightAny :
          (right.language.terms.map (mapGrammarRule rightSymbols)).any
              (constructorCandidate compatible.combinedLanguage.language
                (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
                (rightSymbols.constructor constructor)
                (arguments.map (mapPattern rightSymbols))
                (mapTypeExpr rightSymbols expected)) =
            right.language.terms.any
              (constructorCandidate right.language free bound constructor
                arguments expected) := by
        rw [List.any_map]
        apply list_any_congr_of_mem
        intro rule membership
        exact constructorCandidate_right_source_map compatible constructor
          arguments expected rule
          (checkArguments_right_map_exact compatible
            (fun argument argumentMember argumentExpected =>
              inductionHypothesis argument argumentMember bound
                argumentExpected))
      rw [show compatible.combinedLanguage.language.terms =
        left.language.terms.map (mapGrammarRule leftSymbols) ++
          right.language.terms.map (mapGrammarRule rightSymbols) by rfl]
      rw [List.any_append, leftAny, rightAny, Bool.false_or]
  | hlambda binder body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          simpa [mapPattern, mapTypeExpr, checkHasType] using
            inductionHypothesis (domain :: bound) codomain
      | base sort => simp [mapPattern, mapTypeExpr, checkHasType]
      | multiBinder body => simp [mapPattern, mapTypeExpr, checkHasType]
      | collection collectionType element =>
          simp [mapPattern, mapTypeExpr, checkHasType]
  | hmultiLambda arity binders body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder binderType =>
              simpa [mapPattern, mapTypeExpr, checkHasType, List.map_append,
                List.map_replicate] using
                inductionHypothesis
                  (List.replicate arity binderType ++ bound) codomain
          | base sort => simp [mapPattern, mapTypeExpr, checkHasType]
          | arrow first second => simp [mapPattern, mapTypeExpr, checkHasType]
          | collection collectionType element =>
              simp [mapPattern, mapTypeExpr, checkHasType]
      | base sort => simp [mapPattern, mapTypeExpr, checkHasType]
      | multiBinder body => simp [mapPattern, mapTypeExpr, checkHasType]
      | collection collectionType element =>
          simp [mapPattern, mapTypeExpr, checkHasType]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      rfl
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsExact : ∀ elementType,
          checkElementsHaveType compatible.combinedLanguage.language
              (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
              (elements.map (mapPattern rightSymbols))
              (mapTypeExpr rightSymbols elementType) =
            checkElementsHaveType right.language free bound elements
              elementType := fun elementType =>
        checkElements_right_map_exact compatible
          (fun element elementMember =>
            inductionHypothesis element elementMember bound elementType)
      have leftAny :
          (left.language.terms.map (mapGrammarRule leftSymbols)).any
              (bareCollectionCandidate compatible.combinedLanguage.language
                (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
                collectionType (elements.map (mapPattern rightSymbols))
                (mapTypeExpr rightSymbols expected)) = false := by
        rw [List.any_map, List.any_eq_false]
        intro rule membership
        simp only [Function.comp_apply]
        rw [bareCollectionCandidate_left_map_eq_false_on_right compatible
          collectionType elements expected rule]
        exact Bool.false_ne_true
      have rightAny :
          (right.language.terms.map (mapGrammarRule rightSymbols)).any
              (bareCollectionCandidate compatible.combinedLanguage.language
                (free.map rightSymbols) (bound.map (mapTypeExpr rightSymbols))
                collectionType (elements.map (mapPattern rightSymbols))
                (mapTypeExpr rightSymbols expected)) =
            right.language.terms.any
              (bareCollectionCandidate right.language free bound
                collectionType elements expected) := by
        rw [List.any_map]
        apply list_any_congr_of_mem
        intro rule membership
        exact bareCollectionCandidate_right_source_map compatible
          collectionType elements expected rule elementsExact
      have directExact := directCollection_right_map_exact compatible
        collectionType elements expected elementsExact
      have authoredExact :
          ((left.language.terms.map (mapGrammarRule leftSymbols)).any
              (bareCollectionCandidate compatible.combinedLanguage.language
                (free.map rightSymbols)
                (bound.map (mapTypeExpr rightSymbols)) collectionType
                (elements.map (mapPattern rightSymbols))
                (mapTypeExpr rightSymbols expected)) ||
            (right.language.terms.map (mapGrammarRule rightSymbols)).any
              (bareCollectionCandidate compatible.combinedLanguage.language
                (free.map rightSymbols)
                (bound.map (mapTypeExpr rightSymbols)) collectionType
                (elements.map (mapPattern rightSymbols))
                (mapTypeExpr rightSymbols expected))) =
            right.language.terms.any
              (bareCollectionCandidate right.language free bound collectionType
                elements expected) := by
        rw [leftAny, rightAny, Bool.false_or]
      simp only [mapPattern, mapPatternList_eq_map, checkHasType]
      rw [show compatible.combinedLanguage.language.terms =
        left.language.terms.map (mapGrammarRule leftSymbols) ++
          right.language.terms.map (mapGrammarRule rightSymbols) by rfl]
      rw [List.any_append]
      apply congrArg (fun value : Bool => rest.isNone && value)
      apply congrArg₂ (fun first second : Bool => first || second)
      · exact directExact
      · exact authoredExact

/-- Object-term typing is preserved and reflected exactly on the left image. -/
theorem left_hasType_iff
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {expected : TypeExpr}
    (object : isObjectPattern pattern = true) :
    HasType compatible.combinedLanguage.language (free.map leftSymbols)
        (bound.map (mapTypeExpr leftSymbols))
        (mapPattern leftSymbols pattern) (mapTypeExpr leftSymbols expected) ↔
      HasType left.language free bound pattern expected := by
  have mappedObject : isObjectPattern (mapPattern leftSymbols pattern) = true := by
    simpa [isObjectPattern_mapPattern] using object
  rw [← checkHasType_eq_true_iff mappedObject,
    ← checkHasType_eq_true_iff object,
    left_checkHasType_exact compatible]

/-- Object-term typing is preserved and reflected exactly on the right image. -/
theorem right_hasType_iff
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {expected : TypeExpr}
    (object : isObjectPattern pattern = true) :
    HasType compatible.combinedLanguage.language (free.map rightSymbols)
        (bound.map (mapTypeExpr rightSymbols))
        (mapPattern rightSymbols pattern) (mapTypeExpr rightSymbols expected) ↔
      HasType right.language free bound pattern expected := by
  have mappedObject : isObjectPattern (mapPattern rightSymbols pattern) = true := by
    simpa [isObjectPattern_mapPattern] using object
  rw [← checkHasType_eq_true_iff mappedObject,
    ← checkHasType_eq_true_iff object,
    right_checkHasType_exact compatible]

#print axioms left_checkHasType_exact
#print axioms left_hasType_iff
#print axioms right_checkHasType_exact
#print axioms right_hasType_iff

end Mettapedia.GSLT.LanguageDef.StructuralCoproductTyping
