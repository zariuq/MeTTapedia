import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Executable checking for declaration-derived open typing

This module compiles the existing `WellSorted.HasType` judgment directly from
the sole authored `LanguageDef`.  It does not introduce another typing
relation: the Boolean functions below are executable views whose soundness
and object-pattern completeness are proved against that inductive judgment.

Checking is bidirectional.  The expected type is supplied by the open fiber;
constructor labels select their authored declarations, binder domains come
from the expected arrow type, and bare collection representations search the
finite declaration list.  Explicit substitutions are schema machinery rather
than object terms, so the object checker rejects them.
-/

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Executable view of the representation form selected by one parameter. -/
def matchesParameterRepresentation?
    (parameter : TermParam) (pattern : Pattern) : Bool :=
  match parameter, pattern with
  | .simple _ _, _ => true
  | .abstractionNamed _ _ _, .lambda none _ => true
  | .multiAbstractionNamed _ _ _, .multiLambda _ [] _ => true
  | _, _ => false

@[simp]
theorem matchesParameterRepresentation?_eq_true_iff
    (parameter : TermParam) (pattern : Pattern) :
    matchesParameterRepresentation? parameter pattern = true ↔
      MatchesParameterRepresentation parameter pattern := by
  cases parameter with
  | simple parameterName parameterType =>
      cases pattern <;>
        simp [matchesParameterRepresentation?, MatchesParameterRepresentation]
  | abstractionNamed binderName bodyName parameterType =>
      cases pattern <;>
        simp [matchesParameterRepresentation?, MatchesParameterRepresentation]
      case lambda binder body =>
        cases binder <;>
          simp
  | multiAbstractionNamed binderNames bodyName parameterType =>
      cases pattern <;>
        simp [matchesParameterRepresentation?, MatchesParameterRepresentation]
      case multiLambda arity binders body =>
        cases binders <;>
          simp

/-- Executable recognition of the declaration shape represented by a bare
collection node. -/
def usesBareCollection? (rule : GrammarRule) : Bool :=
  match rule.params with
  | [.simple _ (.collection _ _)] => true
  | _ => false

@[simp]
theorem usesBareCollection?_eq_true_iff (rule : GrammarRule) :
    usesBareCollection? rule = true ↔ UsesBareCollection rule := by
  cases rule with
  | mk label category parameters syntaxPattern evalPolicy =>
      cases parameters with
      | nil => simp [usesBareCollection?, UsesBareCollection]
      | cons parameter remaining =>
          cases remaining with
          | nil =>
              cases parameter <;>
                simp [usesBareCollection?, UsesBareCollection]
              case simple name type =>
                cases type <;> simp
          | cons next tail =>
              simp [usesBareCollection?, UsesBareCollection]

/-- A declaration can type one bare collection at the requested result type
exactly when this function returns its element type. -/
def bareCollectionElementType? (rule : GrammarRule)
    (collectionType : CollType) (expected : TypeExpr) : Option TypeExpr :=
  match expected, rule.params with
  | .base category, [.simple _ (.collection actual elementType)] =>
      if rule.category = category ∧ actual = collectionType then
        some elementType
      else
        none
  | _, _ => none

@[simp]
theorem bareCollectionElementType?_eq_some_iff
    (rule : GrammarRule) (collectionType : CollType)
    (expected elementType : TypeExpr) :
    bareCollectionElementType? rule collectionType expected = some elementType ↔
      expected = .base rule.category ∧
        ∃ parameterName,
          rule.params =
            [.simple parameterName (.collection collectionType elementType)] := by
  cases rule with
  | mk label category parameters syntaxPattern evalPolicy =>
      cases expected <;> cases parameters with
      | nil => simp [bareCollectionElementType?]
      | cons parameter parameters =>
          cases parameters with
          | nil =>
              cases parameter with
              | simple parameterName parameterType =>
                  cases parameterType <;>
                    simp [bareCollectionElementType?] <;> aesop
              | abstractionNamed binderName bodyName parameterType =>
                  simp [bareCollectionElementType?]
              | multiAbstractionNamed binderNames bodyName parameterType =>
                  simp [bareCollectionElementType?]
          | cons next remaining => simp [bareCollectionElementType?]

mutual
  /-- Check one raw pattern against an expected type in the exact authored
  free and bound contexts. -/
  def checkHasType (language : LanguageDef) (free : FreeTypeContext)
      (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) : Bool :=
    match pattern with
    | .bvar index => bound[index]? == some expected
    | .fvar name => free name == some expected
    | .apply constructor arguments =>
        language.terms.any fun rule =>
          rule.label == constructor &&
            expected == .base rule.category &&
            !usesBareCollection? rule &&
            checkArgumentsHaveTypes language free bound arguments rule.params
    | .lambda _ body =>
        match expected with
        | .arrow domain codomain =>
            checkHasType language free (domain :: bound) body codomain
        | _ => false
    | .multiLambda arity _ body =>
        match expected with
        | .arrow (.multiBinder domain) codomain =>
            checkHasType language free
              (List.replicate arity domain ++ bound) body codomain
        | _ => false
    | .subst _ _ => false
    | .collection collectionType elements rest =>
        let direct :=
          match expected with
          | .collection actual elementType =>
              actual == collectionType &&
                checkElementsHaveType language free bound elements elementType
          | _ => false
        let authored := language.terms.any fun rule =>
          match bareCollectionElementType? rule collectionType expected with
          | some elementType =>
              checkElementsHaveType language free bound elements elementType
          | none => false
        rest.isNone && (direct || authored)

  /-- Ordered argument-spine checker compiled from the authored parameter
  list. -/
  def checkArgumentsHaveTypes (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) :
      List Pattern → List TermParam → Bool
    | [], [] => true
    | argument :: arguments, parameter :: parameters =>
        match parameterType? parameter with
        | some expected =>
            matchesParameterRepresentation? parameter argument &&
              checkHasType language free bound argument expected &&
              checkArgumentsHaveTypes language free bound arguments parameters
        | none => false
    | _, _ => false

  /-- Pointwise checker for collection elements. -/
  def checkElementsHaveType (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) :
      List Pattern → TypeExpr → Bool
    | [], _ => true
    | element :: elements, elementType =>
        checkHasType language free bound element elementType &&
          checkElementsHaveType language free bound elements elementType
end

/-- Soundness of the argument-spine checker, assuming soundness for every
immediate argument pattern. -/
theorem checkArgumentsHaveTypes_sound_of
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (argumentSound : ∀ argument ∈ arguments, ∀ expected,
      checkHasType language free bound argument expected = true →
        HasType language free bound argument expected)
    (checked : checkArgumentsHaveTypes language free bound
      arguments parameters = true) :
    ArgumentsHaveTypes language free bound arguments parameters := by
  induction arguments generalizing parameters with
  | nil =>
      cases parameters with
      | nil => exact .nil
      | cons parameter parameters =>
          simp [checkArgumentsHaveTypes] at checked
  | cons argument arguments inductionHypothesis =>
      cases parameters with
      | nil => simp [checkArgumentsHaveTypes] at checked
      | cons parameter parameters =>
          cases parameterTypeEquation : parameterType? parameter with
          | none =>
              simp [checkArgumentsHaveTypes, parameterTypeEquation] at checked
          | some expected =>
              simp only [checkArgumentsHaveTypes, parameterTypeEquation,
                Bool.and_eq_true] at checked
              rcases checked with
                ⟨⟨representationChecked, argumentChecked⟩, argumentsChecked⟩
              exact .cons
                ((matchesParameterRepresentation?_eq_true_iff
                  parameter argument).mp representationChecked)
                parameterTypeEquation
                (argumentSound argument (by simp) expected argumentChecked)
                (inductionHypothesis
                  (fun other membership otherExpected otherChecked =>
                    argumentSound other (by simp [membership])
                      otherExpected otherChecked)
                  argumentsChecked)

/-- Soundness of the collection-element checker, assuming soundness for every
immediate element pattern. -/
theorem checkElementsHaveType_sound_of
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (elementSound : ∀ element ∈ elements,
      checkHasType language free bound element elementType = true →
        HasType language free bound element elementType)
    (checked : checkElementsHaveType language free bound
      elements elementType = true) :
    ElementsHaveType language free bound elements elementType := by
  induction elements with
  | nil => exact .nil bound elementType
  | cons element elements inductionHypothesis =>
      simp only [checkElementsHaveType, Bool.and_eq_true] at checked
      exact .cons
        (elementSound element (by simp) checked.1)
        (inductionHypothesis
          (fun other membership otherChecked =>
            elementSound other (by simp [membership]) otherChecked)
          checked.2)

/-- Every successful executable check is a derivation in the sole declarative
typing relation authored by `LanguageDef`. -/
theorem checkHasType_sound
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (checked : checkHasType language free bound pattern expected = true) :
    HasType language free bound pattern expected := by
  induction pattern using Pattern.inductionOn generalizing bound expected with
  | hbvar index =>
      simp only [checkHasType, beq_iff_eq] at checked
      exact .bvar checked
  | hfvar name =>
      simp only [checkHasType, beq_iff_eq] at checked
      exact .fvar checked
  | happly constructor arguments inductionHypothesis =>
      simp only [checkHasType, List.any_eq_true, Bool.and_eq_true,
        beq_iff_eq, Bool.not_eq_true'] at checked
      obtain ⟨rule, ruleMember,
        ⟨⟨⟨labelEquality, expectedEquality⟩, notBare⟩,
          argumentsChecked⟩⟩ := checked
      subst constructor
      subst expected
      exact .constructor ruleMember
        (by
          intro bare
          have bareChecked :=
            (usesBareCollection?_eq_true_iff rule).mpr bare
          rw [bareChecked] at notBare
          contradiction)
        (checkArgumentsHaveTypes_sound_of
          (fun argument membership argumentExpected argumentChecked =>
            inductionHypothesis argument membership argumentChecked)
          argumentsChecked)
  | hlambda binder body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          exact .lambda (inductionHypothesis checked)
      | base sort => simp [checkHasType] at checked
      | multiBinder type => simp [checkHasType] at checked
      | collection collectionType elementType =>
          simp [checkHasType] at checked
  | hmultiLambda arity binders body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder binderType =>
              exact .multiLambda (inductionHypothesis checked)
          | base sort => simp [checkHasType] at checked
          | arrow first second => simp [checkHasType] at checked
          | collection collectionType elementType =>
              simp [checkHasType] at checked
      | base sort => simp [checkHasType] at checked
      | multiBinder type => simp [checkHasType] at checked
      | collection collectionType elementType =>
          simp [checkHasType] at checked
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [checkHasType] at checked
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [checkHasType, Bool.and_eq_true,
        Bool.or_eq_true, List.any_eq_true] at checked
      rcases checked with ⟨restIsNone, directOrAuthored⟩
      cases directOrAuthored with
      | inl direct =>
          cases expected with
          | collection actual elementType =>
              simp only [Bool.and_eq_true, beq_iff_eq] at direct
              rcases direct with ⟨actualEquality, elementsChecked⟩
              subst actual
              exact .collection
                (checkElementsHaveType_sound_of
                  (fun element membership elementChecked =>
                    inductionHypothesis element membership elementChecked)
                  elementsChecked)
          | base sort => simp at direct
          | arrow domain codomain => simp at direct
          | multiBinder type => simp at direct
      | inr authored =>
          obtain ⟨rule, ruleMember, ruleChecked⟩ := authored
          generalize elementTypeEquation :
            bareCollectionElementType? rule collectionType expected = result
              at ruleChecked
          cases result with
          | none => simp at ruleChecked
          | some elementType =>
            rw [bareCollectionElementType?_eq_some_iff] at elementTypeEquation
            rcases elementTypeEquation with
              ⟨expectedEquality, parameterName, parameterShape⟩
            subst expected
            exact .collectionConstructor ruleMember parameterShape
              (checkElementsHaveType_sound_of
                (fun element membership elementChecked =>
                  inductionHypothesis element membership elementChecked)
                ruleChecked)

/-- Every successful homogeneous element-spine check is a derivation in the
sole authored typing relation. -/
theorem checkElementsHaveType_sound
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (checked : checkElementsHaveType language free bound elements
      elementType = true) :
    ElementsHaveType language free bound elements elementType := by
  exact checkElementsHaveType_sound_of
    (fun _element _membership elementChecked =>
      checkHasType_sound elementChecked)
    checked

mutual
  /-- Every declaratively typed object pattern is accepted by the executable
  checker.  The object premise excludes schema-only substitutions and open
  collection tails, exactly matching the executable carrier. -/
  theorem checkHasType_complete_of_object
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
      (typed : HasType language free bound pattern expected)
      (object : isObjectPattern pattern = true) :
      checkHasType language free bound pattern expected = true := by
    cases typed with
    | bvar lookup => simp [checkHasType, lookup]
    | fvar lookup => simp [checkHasType, lookup]
    | @constructor bound rule arguments ruleMember notBare argumentsTyped =>
        simp only [isObjectPattern] at object
        have notBareChecked : usesBareCollection? rule = false := by
          apply Bool.eq_false_of_not_eq_true
          intro bareChecked
          exact notBare
            ((usesBareCollection?_eq_true_iff rule).mp bareChecked)
        simp only [checkHasType, List.any_eq_true]
        exact ⟨rule, ruleMember, by
          simp [notBareChecked,
            checkArgumentsHaveTypes_complete_of_objects
              argumentsTyped object]⟩
    | @lambda bound binder body domain codomain bodyTyped =>
        simp only [isObjectPattern] at object
        simpa [checkHasType] using
          checkHasType_complete_of_object bodyTyped object
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        simp only [isObjectPattern] at object
        simpa [checkHasType] using
          checkHasType_complete_of_object bodyTyped object
    | subst bodyTyped replacementTyped =>
        simp [isObjectPattern] at object
    | @collection bound collectionType elements rest elementType elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        have elementsChecked :=
          checkElementsHaveType_complete_of_objects elementsTyped object.2
        simp [checkHasType, object.1, elementsChecked]
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType ruleMember parameterShape elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        have elementTypeEquation :
            bareCollectionElementType? rule collectionType
                (.base rule.category) = some elementType :=
          (bareCollectionElementType?_eq_some_iff rule collectionType
            (.base rule.category) elementType).mpr
              ⟨rfl, parameterName, parameterShape⟩
        have elementsChecked :=
          checkElementsHaveType_complete_of_objects elementsTyped object.2
        simp only [checkHasType, object.1, Bool.true_and, Bool.or_eq_true,
          List.any_eq_true]
        exact Or.inr ⟨rule, ruleMember, by
          rw [elementTypeEquation]
          exact elementsChecked⟩

  /-- Completeness companion for ordered constructor arguments. -/
  theorem checkArgumentsHaveTypes_complete_of_objects
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters)
      (objects : isObjectPatternList arguments = true) :
      checkArgumentsHaveTypes language free bound arguments parameters = true := by
    cases typed with
    | nil => rfl
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        simp only [checkArgumentsHaveTypes, parameterType, Bool.and_eq_true]
        exact ⟨⟨
          (matchesParameterRepresentation?_eq_true_iff
            parameter argument).mpr representation,
          checkHasType_complete_of_object argumentTyped objects.1⟩,
          checkArgumentsHaveTypes_complete_of_objects
            argumentsTyped objects.2⟩

  /-- Completeness companion for collection elements. -/
  theorem checkElementsHaveType_complete_of_objects
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType)
      (objects : isObjectPatternList elements = true) :
      checkElementsHaveType language free bound elements elementType = true := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        simp only [checkElementsHaveType, Bool.and_eq_true]
        exact ⟨checkHasType_complete_of_object elementTyped objects.1,
          checkElementsHaveType_complete_of_objects elementsTyped objects.2⟩
end

/-- On object patterns, executable checking is exactly the sole declarative
typing relation rather than a parallel approximation. -/
theorem checkHasType_eq_true_iff
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (object : isObjectPattern pattern = true) :
    checkHasType language free bound pattern expected = true ↔
      HasType language free bound pattern expected :=
  ⟨checkHasType_sound, fun typed =>
    checkHasType_complete_of_object typed object⟩

/-! ## Executable admission of the complete open core carrier -/

/-- Executable ordinary scope check at the ambient binder depth. -/
def checkScopeSafeAt (depth : Nat) (pattern : Pattern) : Bool :=
  pattern.isWellScopedAt depth

@[simp]
theorem checkScopeSafeAt_eq_true_iff (depth : Nat) (pattern : Pattern) :
    checkScopeSafeAt depth pattern = true ↔ ScopeSafeAt depth pattern := by
  rfl

/-- One executable admission check for the arbitrary-type open object
carrier.  Typing, binder metadata, schema elimination, and ordinary scope
remain distinct conjuncts even though the runtime exposes one Boolean. -/
def checkOpenPatternWellSorted (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (pattern : Pattern) : Bool :=
  checkHasType language free bound pattern expected &&
    pattern.hasCanonicalBinderMetadata &&
    isObjectPattern pattern &&
    checkScopeSafeAt bound.length pattern

/-- Successful executable admission constructs evidence in the sole
declarative open-pattern carrier. -/
theorem checkOpenPatternWellSorted_sound
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (checked : checkOpenPatternWellSorted language free bound expected pattern =
      true) :
    OpenPatternWellSorted language free bound expected pattern := by
  simp only [checkOpenPatternWellSorted, Bool.and_eq_true] at checked
  exact ⟨checkHasType_sound checked.1.1.1, checked.1.1.2, checked.1.2,
    (checkScopeSafeAt_eq_true_iff bound.length pattern).mp checked.2⟩

/-- Every genuine arbitrary-type open object is accepted by the executable
admission check. -/
theorem checkOpenPatternWellSorted_complete
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (wellSorted : OpenPatternWellSorted language free bound expected pattern) :
    checkOpenPatternWellSorted language free bound expected pattern = true := by
  rcases wellSorted with ⟨typed, canonical, object, scopeProof⟩
  simp [checkOpenPatternWellSorted,
    checkHasType_complete_of_object typed object, canonical, object,
    (checkScopeSafeAt_eq_true_iff bound.length pattern).mpr scopeProof]

/-- Executable open-pattern admission is neither weaker nor stronger than
the declaration-derived carrier. -/
theorem checkOpenPatternWellSorted_eq_true_iff
    (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern) :
    checkOpenPatternWellSorted language free bound expected pattern = true ↔
      OpenPatternWellSorted language free bound expected pattern :=
  ⟨checkOpenPatternWellSorted_sound, checkOpenPatternWellSorted_complete⟩

end Mettapedia.GSLT.LanguageDef.WellSorted
