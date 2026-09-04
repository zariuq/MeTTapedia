import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Sorting the complete LanguageDef carrier

`WellSorted.HasType` derives the recursive AST carrier from constructor rows.
This companion judgment additionally admits atomic patterns through the
carrier declared for their expected sort.  It is needed for languages that
mix authored AST structure with builtin integers or strings; the carrier row,
not an ambient host convention, remains the authority.
-/

namespace Mettapedia.GSLT.LanguageDef.CarrierWellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

def carrierAcceptsAtom (carrier : CarrierKind) (atom : String) : Bool :=
  match carrier with
  | .builtinString => true
  | .builtinInt => atom.toInt?.isSome
  | _ => false

def BuiltinAtomHasType (language : LanguageDef) (atom : String)
    (expected : TypeExpr) : Prop :=
  ∃ declaration : TypeDecl, List.Mem declaration language.types ∧
    expected = .base declaration.name ∧
      carrierAcceptsAtom declaration.carrier atom = true

def checkBuiltinAtomHasType (language : LanguageDef) (atom : String)
    (expected : TypeExpr) : Bool :=
  language.types.any fun declaration =>
    expected == .base declaration.name &&
      carrierAcceptsAtom declaration.carrier atom

theorem checkBuiltinAtomHasType_eq_true_iff
    (language : LanguageDef) (atom : String) (expected : TypeExpr) :
    checkBuiltinAtomHasType language atom expected = true ↔
      BuiltinAtomHasType language atom expected := by
  unfold checkBuiltinAtomHasType BuiltinAtomHasType
  rw [List.any_eq_true]
  constructor
  · rintro ⟨declaration, membership, checked⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    exact ⟨declaration, membership, checked.1, checked.2⟩
  · rintro ⟨declaration, membership, typeEquality, accepted⟩
    exact ⟨declaration, membership, by
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨typeEquality, accepted⟩⟩

mutual
  inductive HasType (language : LanguageDef) (free : FreeTypeContext) :
      List TypeExpr → Pattern → TypeExpr → Prop where
    | bvar {bound : List TypeExpr} {index : Nat} {type : TypeExpr} :
        bound[index]? = some type →
        HasType language free bound (.bvar index) type
    | fvar {bound : List TypeExpr} {name : String} {type : TypeExpr} :
        free name = some type →
        HasType language free bound (.fvar name) type
    | builtinAtom
        {bound : List TypeExpr} {atom : String} {type : TypeExpr} :
        BuiltinAtomHasType language atom type →
        HasType language free bound (.apply atom []) type
    | constructor
        {bound : List TypeExpr} {rule : GrammarRule} {arguments : List Pattern} :
        rule ∈ language.terms →
        ¬ UsesBareCollection rule →
        ArgumentsHaveTypes language free bound arguments rule.params →
        HasType language free bound (.apply rule.label arguments)
          (.base rule.category)
    | lambda
        {bound : List TypeExpr} {binder : Option String} {body : Pattern}
        {domain codomain : TypeExpr} :
        HasType language free (domain :: bound) body codomain →
        HasType language free bound (.lambda binder body)
          (.arrow domain codomain)
    | multiLambda
        {bound : List TypeExpr} {arity : Nat} {binders : List String}
        {body : Pattern} {domain codomain : TypeExpr} :
        HasType language free (List.replicate arity domain ++ bound) body codomain →
        HasType language free bound (.multiLambda arity binders body)
          (.arrow (.multiBinder domain) codomain)
    | subst
        {bound : List TypeExpr} {body replacement : Pattern}
        {domain codomain : TypeExpr} :
        HasType language free (domain :: bound) body codomain →
        HasType language free bound replacement domain →
        HasType language free bound (.subst body replacement) codomain
    | collection
        {bound : List TypeExpr} {collectionType : CollType}
        {elements : List Pattern} {rest : Option String} {elementType : TypeExpr} :
        ElementsHaveTypes language free bound elements elementType →
        HasType language free bound
          (.collection collectionType elements rest)
          (.collection collectionType elementType)
    | collectionConstructor
        {bound : List TypeExpr} {rule : GrammarRule} {parameterName : String}
        {collectionType : CollType} {elements : List Pattern}
        {rest : Option String} {elementType : TypeExpr} :
        rule ∈ language.terms →
        rule.params =
          [.simple parameterName (.collection collectionType elementType)] →
        ElementsHaveTypes language free bound elements elementType →
        HasType language free bound
          (.collection collectionType elements rest) (.base rule.category)

  inductive ArgumentsHaveTypes (language : LanguageDef)
      (free : FreeTypeContext) :
      List TypeExpr → List Pattern → List TermParam → Prop where
    | nil {bound : List TypeExpr} :
        ArgumentsHaveTypes language free bound [] []
    | cons
        {argument : Pattern} {arguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {bound : List TypeExpr} {expected : TypeExpr} :
        MatchesParameterRepresentation parameter argument →
        parameterType? parameter = some expected →
        HasType language free bound argument expected →
        ArgumentsHaveTypes language free bound arguments parameters →
        ArgumentsHaveTypes language free bound
          (argument :: arguments) (parameter :: parameters)

  inductive ElementsHaveTypes (language : LanguageDef)
      (free : FreeTypeContext) :
      List TypeExpr → List Pattern → TypeExpr → Prop where
    | nil {bound : List TypeExpr} {elementType : TypeExpr} :
        ElementsHaveTypes language free bound [] elementType
    | cons
        {bound : List TypeExpr} {element : Pattern} {elements : List Pattern}
        {elementType : TypeExpr} :
        HasType language free bound element elementType →
        ElementsHaveTypes language free bound elements elementType →
        ElementsHaveTypes language free bound (element :: elements) elementType
end

mutual
  def checkHasType (language : LanguageDef) (free : FreeTypeContext)
      (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) : Bool :=
    match pattern with
    | .bvar index => bound[index]? == some expected
    | .fvar name => free name == some expected
    | .apply constructor arguments =>
        (arguments.isEmpty &&
          checkBuiltinAtomHasType language constructor expected) ||
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
                checkElementsHaveTypes language free bound elements elementType
          | _ => false
        let authored := language.terms.any fun rule =>
          match bareCollectionElementType? rule collectionType expected with
          | some elementType =>
              checkElementsHaveTypes language free bound elements elementType
          | none => false
        rest.isNone && (direct || authored)

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

  def checkElementsHaveTypes (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) :
      List Pattern → TypeExpr → Bool
    | [], _ => true
    | element :: elements, elementType =>
      checkHasType language free bound element elementType &&
          checkElementsHaveTypes language free bound elements elementType
end

/-- Successful checking consumes exactly one argument for each authored
constructor parameter.  This small inversion theorem is useful to clients
that recover constructor spines from the generic executable checker. -/
theorem checkArgumentsHaveTypes_length_eq
    (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (arguments : List Pattern)
    (parameters : List TermParam)
    (checked : checkArgumentsHaveTypes language free bound
      arguments parameters = true) :
    arguments.length = parameters.length := by
  induction arguments generalizing parameters with
  | nil =>
      cases parameters with
      | nil => rfl
      | cons parameter parameters =>
          simp [checkArgumentsHaveTypes] at checked
  | cons argument arguments inductionHypothesis =>
      cases parameters with
      | nil => simp [checkArgumentsHaveTypes] at checked
      | cons parameter parameters =>
          cases equation : parameterType? parameter with
          | none => simp [checkArgumentsHaveTypes, equation] at checked
          | some expected =>
              simp only [checkArgumentsHaveTypes, equation,
                Bool.and_eq_true] at checked
              simp [inductionHypothesis parameters checked.2]

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

theorem checkElementsHaveTypes_sound_of
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (elementSound : ∀ element ∈ elements,
      checkHasType language free bound element elementType = true →
        HasType language free bound element elementType)
    (checked : checkElementsHaveTypes language free bound
      elements elementType = true) :
    ElementsHaveTypes language free bound elements elementType := by
  induction elements with
  | nil => exact .nil
  | cons element elements inductionHypothesis =>
      simp only [checkElementsHaveTypes, Bool.and_eq_true] at checked
      exact .cons
        (elementSound element (by simp) checked.1)
        (inductionHypothesis
          (fun other membership otherChecked =>
            elementSound other (by simp [membership]) otherChecked)
          checked.2)

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
      simp only [checkHasType, Bool.or_eq_true, Bool.and_eq_true] at checked
      cases checked with
      | inl builtinChecked =>
          rcases builtinChecked with ⟨empty, atomChecked⟩
          have argumentsEmpty : arguments = [] := List.isEmpty_iff.mp empty
          subst arguments
          exact .builtinAtom
            ((checkBuiltinAtomHasType_eq_true_iff
              language constructor expected).mp atomChecked)
      | inr constructorChecked =>
          simp only [List.any_eq_true, Bool.and_eq_true,
            beq_iff_eq, Bool.not_eq_true'] at constructorChecked
          obtain ⟨rule, ruleMember,
            ⟨⟨⟨labelEquality, expectedEquality⟩, notBare⟩,
              argumentsChecked⟩⟩ := constructorChecked
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
              exact HasType.collection
                (checkElementsHaveTypes_sound_of
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
            exact HasType.collectionConstructor ruleMember parameterShape
              (checkElementsHaveTypes_sound_of
                (fun element membership elementChecked =>
                  inductionHypothesis element membership elementChecked)
                ruleChecked)

mutual
  /-- Every declaratively typed carrier object is accepted by the executable
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
    | builtinAtom atomTyped =>
        simp only [checkHasType, Bool.or_eq_true]
        exact Or.inl
          ((checkBuiltinAtomHasType_eq_true_iff language _ _).mpr atomTyped)
    | @constructor bound rule arguments ruleMember notBare argumentsTyped =>
        simp only [isObjectPattern] at object
        have notBareChecked : usesBareCollection? rule = false := by
          apply Bool.eq_false_of_not_eq_true
          intro bareChecked
          exact notBare
            ((usesBareCollection?_eq_true_iff rule).mp bareChecked)
        simp only [checkHasType, Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨rule, ruleMember, by
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
          checkElementsHaveTypes_complete_of_objects elementsTyped object.2
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
          checkElementsHaveTypes_complete_of_objects elementsTyped object.2
        simp only [checkHasType, object.1, Bool.true_and, Bool.or_eq_true,
          List.any_eq_true]
        exact Or.inr ⟨rule, ruleMember, by
          rw [elementTypeEquation]
          exact elementsChecked⟩

  /-- Completeness companion for ordered carrier constructor arguments. -/
  theorem checkArgumentsHaveTypes_complete_of_objects
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters)
      (objects : isObjectPatternList arguments = true) :
      checkArgumentsHaveTypes language free bound arguments parameters = true := by
    cases typed with
    | nil => rfl
    | @cons argument arguments parameter parameters bound expected
        representation parameterType argumentTyped argumentsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        simp only [checkArgumentsHaveTypes, parameterType, Bool.and_eq_true]
        exact ⟨⟨
          (matchesParameterRepresentation?_eq_true_iff
            parameter argument).mpr representation,
          checkHasType_complete_of_object argumentTyped objects.1⟩,
          checkArgumentsHaveTypes_complete_of_objects
            argumentsTyped objects.2⟩

  /-- Completeness companion for homogeneous carrier collection elements. -/
  theorem checkElementsHaveTypes_complete_of_objects
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveTypes language free bound elements elementType)
      (objects : isObjectPatternList elements = true) :
      checkElementsHaveTypes language free bound elements elementType = true := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        simp only [checkElementsHaveTypes, Bool.and_eq_true]
        exact ⟨checkHasType_complete_of_object elementTyped objects.1,
          checkElementsHaveTypes_complete_of_objects
            elementsTyped objects.2⟩
end

/-- On object patterns, executable carrier checking is exactly the declarative
typing relation rather than a parallel approximation. -/
theorem checkHasType_eq_true_iff
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (object : isObjectPattern pattern = true) :
    checkHasType language free bound pattern expected = true ↔
      HasType language free bound pattern expected :=
  ⟨checkHasType_sound, fun typed =>
    checkHasType_complete_of_object typed object⟩

theorem builtin_string_positive :
    checkBuiltinAtomHasType
      { name := "literal-canary", types := [
          { name := "String", carrier := .builtinString }],
        terms := [], equations := [], rewrites := [] }
      "hello" (.base "String") = true := by
  decide

theorem non_builtin_carrier_negative :
    checkBuiltinAtomHasType
      { name := "literal-canary", types := [
          { name := "Tree", carrier := .ast }],
        terms := [], equations := [], rewrites := [] }
      "not-a-tree-constructor" (.base "Tree") = false := by
  rfl

#print axioms checkHasType_sound
#print axioms checkHasType_complete_of_object
#print axioms checkHasType_eq_true_iff
#print axioms checkArgumentsHaveTypes_length_eq

end Mettapedia.GSLT.LanguageDef.CarrierWellSorted
