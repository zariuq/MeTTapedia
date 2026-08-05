import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Typing inversion along one-hole contexts

The alignment classifier walks one authored occurrence context through two
typed endpoints simultaneously.  This module supplies the typing side of
that walk: splitting an argument or element spine at the active position,
inverting an application or collection judgment, and descending a complete
`OneHoleContext` through two derivations of one shared result type to a
shared hole fibre.

Two determinism hypotheses make the shared fibre honest: distinct authored
rules must not share a wire label, and a collection at one collection type
and result category must select one element type.  Explicit-substitution
frames are impossible for object patterns and are discharged rather than
inverted.
-/

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- The active element of an object-pattern list is an object pattern. -/
theorem isObjectPatternList_append_cons
    {before : List Pattern} {middle : Pattern} {after : List Pattern}
    (object : isObjectPatternList (before ++ middle :: after) = true) :
    isObjectPattern middle = true := by
  induction before with
  | nil =>
      simp only [List.nil_append, isObjectPatternList,
        Bool.and_eq_true] at object
      exact object.1
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, isObjectPatternList,
        Bool.and_eq_true] at object
      exact inductionHypothesis object.2

/-- Split a typed argument spine at the active position, retaining the exact
parameter, expected type, and both sibling spines. -/
theorem ArgumentsHaveTypes.append_cons_split
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} :
    ∀ {before : List Pattern} {middle : Pattern} {after : List Pattern}
      {parameters : List TermParam},
      ArgumentsHaveTypes language free bound (before ++ middle :: after)
        parameters →
      ∃ beforeParameters parameter afterParameters expected,
        parameters = beforeParameters ++ parameter :: afterParameters ∧
        beforeParameters.length = before.length ∧
        ArgumentsHaveTypes language free bound before beforeParameters ∧
        MatchesParameterRepresentation parameter middle ∧
        parameterType? parameter = some expected ∧
        HasType language free bound middle expected ∧
        ArgumentsHaveTypes language free bound after afterParameters
  | [], middle, after, parameters, typed => by
      cases typed with
      | cons representation parameterType middleTyped afterTyped =>
          exact ⟨[], _, _, _, rfl, rfl, .nil, representation, parameterType,
            middleTyped, afterTyped⟩
  | head :: tail, middle, after, parameters, typed => by
      cases typed with
      | cons representation parameterType headTyped tailTyped =>
          obtain ⟨beforeParameters, parameter, afterParameters, expected,
              parametersEq, lengthEq, beforeTyped, middleRepresentation,
              middleParameterType, middleTyped, afterTyped⟩ :=
            ArgumentsHaveTypes.append_cons_split tailTyped
          exact ⟨_ :: beforeParameters, parameter, afterParameters, expected,
            by simp [parametersEq], by simp [lengthEq],
            .cons representation parameterType headTyped beforeTyped,
            middleRepresentation, middleParameterType, middleTyped,
            afterTyped⟩

/-- Split a typed collection spine at the active position. -/
theorem ElementsHaveType.append_cons_split
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elementType : TypeExpr} :
    ∀ {before : List Pattern} {middle : Pattern} {after : List Pattern},
      ElementsHaveType language free bound (before ++ middle :: after)
        elementType →
      ElementsHaveType language free bound before elementType ∧
        HasType language free bound middle elementType ∧
        ElementsHaveType language free bound after elementType
  | [], middle, after, typed => by
      cases typed with
      | cons middleTyped afterTyped =>
          exact ⟨.nil bound elementType, middleTyped, afterTyped⟩
  | head :: tail, middle, after, typed => by
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨beforeTyped, middleTyped, afterTyped⟩ :=
            ElementsHaveType.append_cons_split tailTyped
          exact ⟨.cons headTyped beforeTyped, middleTyped, afterTyped⟩

/-- Single inversion of an application judgment, with every index exposed as
an equation. -/
theorem hasType_apply_inversion
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {label : String} {arguments : List Pattern}
    {type : TypeExpr}
    (typed : HasType language free bound (.apply label arguments) type) :
    ∃ rule, rule ∈ language.terms ∧ label = rule.label ∧
      ¬ UsesBareCollection rule ∧ type = .base rule.category ∧
      ArgumentsHaveTypes language free bound arguments rule.params := by
  cases typed with
  | constructor membership notBare argumentsTyped =>
      exact ⟨_, membership, rfl, notBare, rfl, argumentsTyped⟩

/-- Single inversion of a collection judgment: either a raw collection value
or one authored bare-collection constructor. -/
theorem hasType_collection_inversion
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {collectionType : CollType}
    {elements : List Pattern} {rest : Option String} {type : TypeExpr}
    (typed : HasType language free bound
      (.collection collectionType elements rest) type) :
    (∃ elementType, type = .collection collectionType elementType ∧
        ElementsHaveType language free bound elements elementType) ∨
      (∃ rule parameterName elementType, rule ∈ language.terms ∧
        rule.params =
          [.simple parameterName (.collection collectionType elementType)] ∧
        type = .base rule.category ∧
        ElementsHaveType language free bound elements elementType) := by
  cases typed with
  | collection elementsTyped =>
      exact Or.inl ⟨_, rfl, elementsTyped⟩
  | collectionConstructor membership parameterShape elementsTyped =>
      exact Or.inr ⟨_, _, _, membership, parameterShape, rfl, elementsTyped⟩

/-- Distinct authored rules never share a wire label. -/
def LabelDeterministic (language : LanguageDef) : Prop :=
  ∀ {left right : GrammarRule}, left ∈ language.terms →
    right ∈ language.terms → left.label = right.label → left = right

/-- A collection at one collection type and result category selects one
element type. -/
def CollectionChoiceDeterministic (language : LanguageDef) : Prop :=
  ∀ {leftRule rightRule : GrammarRule} {leftName rightName : String}
    {collectionType : CollType} {leftElementType rightElementType : TypeExpr},
    leftRule ∈ language.terms → rightRule ∈ language.terms →
    leftRule.params =
      [.simple leftName (.collection collectionType leftElementType)] →
    rightRule.params =
      [.simple rightName (.collection collectionType rightElementType)] →
    leftRule.category = rightRule.category →
    leftElementType = rightElementType

/-- Executable check for collection-choice determinism over one authored
term list. -/
def collectionChoiceCheck (terms : List GrammarRule) : Bool :=
  terms.all fun left => terms.all fun right =>
    match left.params, right.params with
    | [.simple _ (.collection leftCollection leftElement)],
      [.simple _ (.collection rightCollection rightElement)] =>
        !(leftCollection == rightCollection &&
            left.category == right.category) ||
          leftElement == rightElement
    | _, _ => true

/-- A successful executable check discharges collection-choice determinism. -/
theorem collectionChoiceDeterministic_of_check {language : LanguageDef}
    (check : collectionChoiceCheck language.terms = true) :
    CollectionChoiceDeterministic language := by
  intro leftRule rightRule leftName rightName collectionType leftElementType
    rightElementType leftMembership rightMembership leftShape rightShape
    categoriesEq
  have leftAll := List.all_eq_true.mp check leftRule leftMembership
  have pairCheck := List.all_eq_true.mp leftAll rightRule rightMembership
  rw [leftShape, rightShape] at pairCheck
  simpa [categoriesEq] using pairCheck

/-- Two application judgments at one label and one result type select one
authored rule, so both argument spines type against the same parameters. -/
theorem hasType_apply_pair
    {language : LanguageDef} {free : FreeTypeContext}
    (deterministic : LabelDeterministic language)
    {bound : List TypeExpr} {label : String}
    {leftArguments rightArguments : List Pattern} {type : TypeExpr}
    (leftTyped : HasType language free bound
      (.apply label leftArguments) type)
    (rightTyped : HasType language free bound
      (.apply label rightArguments) type) :
    ∃ rule, rule ∈ language.terms ∧ label = rule.label ∧
      ¬ UsesBareCollection rule ∧ type = .base rule.category ∧
      ArgumentsHaveTypes language free bound leftArguments rule.params ∧
      ArgumentsHaveTypes language free bound rightArguments rule.params := by
  obtain ⟨leftRule, leftMembership, leftLabel, leftNotBare, leftType,
      leftArgumentsTyped⟩ := hasType_apply_inversion leftTyped
  obtain ⟨rightRule, rightMembership, rightLabel, _, rightType,
      rightArgumentsTyped⟩ := hasType_apply_inversion rightTyped
  have ruleEq : rightRule = leftRule :=
    deterministic rightMembership leftMembership
      (rightLabel.symm.trans leftLabel)
  subst ruleEq
  exact ⟨_, leftMembership, leftLabel, leftNotBare, leftType,
    leftArgumentsTyped, rightArgumentsTyped⟩

/-- Two collection judgments at one collection type and one result type
share one element type. -/
theorem hasType_collection_pair
    {language : LanguageDef} {free : FreeTypeContext}
    (collectionDeterministic : CollectionChoiceDeterministic language)
    {bound : List TypeExpr} {collectionType : CollType}
    {leftElements rightElements : List Pattern} {rest : Option String}
    {type : TypeExpr}
    (leftTyped : HasType language free bound
      (.collection collectionType leftElements rest) type)
    (rightTyped : HasType language free bound
      (.collection collectionType rightElements rest) type) :
    ∃ elementType,
      ElementsHaveType language free bound leftElements elementType ∧
        ElementsHaveType language free bound rightElements elementType := by
  rcases hasType_collection_inversion leftTyped with
    ⟨leftElementType, leftType, leftElementsTyped⟩ |
      ⟨leftRule, leftName, leftElementType, leftMembership, leftShape,
        leftType, leftElementsTyped⟩
  · rcases hasType_collection_inversion rightTyped with
      ⟨rightElementType, rightType, rightElementsTyped⟩ |
        ⟨rightRule, rightName, rightElementType, _, _, rightType, _⟩
    · subst leftType
      have elementTypesEq : leftElementType = rightElementType :=
        (TypeExpr.collection.inj rightType).2
      subst elementTypesEq
      exact ⟨_, leftElementsTyped, rightElementsTyped⟩
    · rw [leftType] at rightType
      exact absurd rightType (by simp)
  · rcases hasType_collection_inversion rightTyped with
      ⟨rightElementType, rightType, rightElementsTyped⟩ |
        ⟨rightRule, rightName, rightElementType, rightMembership, rightShape,
          rightType, rightElementsTyped⟩
    · rw [leftType] at rightType
      exact absurd rightType.symm (by simp)
    · have categoriesEq : leftRule.category = rightRule.category := by
        rw [leftType] at rightType
        exact TypeExpr.base.inj rightType
      have elementTypesEq : leftElementType = rightElementType :=
        collectionDeterministic leftMembership rightMembership leftShape
          rightShape categoriesEq
      subst elementTypesEq
      exact ⟨_, leftElementsTyped, rightElementsTyped⟩

/-- Descend one occurrence context through two typed endpoints of one shared
result type, arriving at one shared hole fibre.  Explicit-substitution
frames are impossible for object endpoints; every other frame either
preserves the bound context or extends it identically on both sides. -/
theorem hasType_fill_pair_decomposition
    {language : LanguageDef} {free : FreeTypeContext}
    (labelDeterministic : LabelDeterministic language)
    (collectionDeterministic : CollectionChoiceDeterministic language) :
    ∀ (context : OneHoleContext) {bound : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      HasType language free bound (context.fill leftPattern) type →
      HasType language free bound (context.fill rightPattern) type →
      isObjectPattern (context.fill leftPattern) = true →
      ∃ holeBound holeType,
        HasType language free (holeBound ++ bound) leftPattern holeType ∧
        HasType language free (holeBound ++ bound) rightPattern holeType := by
  intro context
  induction context with
  | hole =>
      intro bound leftPattern rightPattern type leftTyped rightTyped _
      exact ⟨[], type, by simpa using leftTyped, by simpa using rightTyped⟩
  | apply constructor before inner after inductionHypothesis =>
      intro bound leftPattern rightPattern type leftTyped rightTyped object
      simp only [OneHoleContext.fill] at leftTyped rightTyped object
      obtain ⟨rule, membership, labelEq, notBare, typeEq, leftArguments,
          rightArguments⟩ :=
        hasType_apply_pair labelDeterministic leftTyped rightTyped
      obtain ⟨leftBeforeParameters, leftParameter, leftAfterParameters,
          leftExpected, leftParametersEq, leftLengthEq, _, _,
          leftParameterType, leftMiddleTyped, _⟩ :=
        ArgumentsHaveTypes.append_cons_split leftArguments
      obtain ⟨rightBeforeParameters, rightParameter, rightAfterParameters,
          rightExpected, rightParametersEq, rightLengthEq, _, _,
          rightParameterType, rightMiddleTyped, _⟩ :=
        ArgumentsHaveTypes.append_cons_split rightArguments
      have beforeEq : leftBeforeParameters = rightBeforeParameters ∧
          leftParameter :: leftAfterParameters =
            rightParameter :: rightAfterParameters :=
        List.append_inj (leftParametersEq.symm.trans rightParametersEq)
          (leftLengthEq.trans rightLengthEq.symm)
      have parameterEq : leftParameter = rightParameter :=
        (List.cons.inj beforeEq.2).1
      have expectedEq : leftExpected = rightExpected := by
        have := leftParameterType
        rw [parameterEq, rightParameterType] at this
        exact (Option.some.inj this).symm
      have objectMiddle : isObjectPattern (inner.fill leftPattern) = true := by
        simp only [isObjectPattern] at object
        exact isObjectPatternList_append_cons object
      exact inductionHypothesis leftMiddleTyped
        (expectedEq ▸ rightMiddleTyped) objectMiddle
  | lambda binderName inner inductionHypothesis =>
      intro bound leftPattern rightPattern type leftTyped rightTyped object
      simp only [OneHoleContext.fill] at leftTyped rightTyped object
      cases leftTyped with
      | @lambda _ _ _ domain codomain leftBody =>
          cases rightTyped with
          | lambda rightBody =>
              simp only [isObjectPattern] at object
              obtain ⟨holeBound, holeType, leftHole, rightHole⟩ :=
                inductionHypothesis leftBody rightBody object
              refine ⟨holeBound ++ [domain], holeType, ?_, ?_⟩
              · simpa [List.append_assoc] using leftHole
              · simpa [List.append_assoc] using rightHole
  | multiLambda arity binderNames inner inductionHypothesis =>
      intro bound leftPattern rightPattern type leftTyped rightTyped object
      simp only [OneHoleContext.fill] at leftTyped rightTyped object
      cases leftTyped with
      | @multiLambda _ _ _ _ domain codomain leftBody =>
          cases rightTyped with
          | multiLambda rightBody =>
              simp only [isObjectPattern] at object
              obtain ⟨holeBound, holeType, leftHole, rightHole⟩ :=
                inductionHypothesis leftBody rightBody object
              refine ⟨holeBound ++ List.replicate arity domain, holeType,
                ?_, ?_⟩
              · simpa [List.append_assoc] using leftHole
              · simpa [List.append_assoc] using rightHole
  | substBody inner replacement inductionHypothesis =>
      intro bound leftPattern rightPattern type leftTyped rightTyped object
      simp [OneHoleContext.fill, isObjectPattern] at object
  | substReplacement body inner inductionHypothesis =>
      intro bound leftPattern rightPattern type leftTyped rightTyped object
      simp [OneHoleContext.fill, isObjectPattern] at object
  | collection collectionType before inner after rest inductionHypothesis =>
      intro bound leftPattern rightPattern type leftTyped rightTyped object
      simp only [OneHoleContext.fill] at leftTyped rightTyped object
      obtain ⟨elementType, leftElements, rightElements⟩ :=
        hasType_collection_pair collectionDeterministic leftTyped rightTyped
      obtain ⟨_, leftMiddleTyped, _⟩ :=
        ElementsHaveType.append_cons_split leftElements
      obtain ⟨_, rightMiddleTyped, _⟩ :=
        ElementsHaveType.append_cons_split rightElements
      have objectMiddle : isObjectPattern (inner.fill leftPattern) = true := by
        simp only [isObjectPattern, Bool.and_eq_true] at object
        exact isObjectPatternList_append_cons object.2
      exact inductionHypothesis leftMiddleTyped rightMiddleTyped objectMiddle

end Mettapedia.GSLT.LanguageDef.WellSorted
