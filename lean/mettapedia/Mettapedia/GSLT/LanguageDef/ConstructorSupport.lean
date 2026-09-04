import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Constructor support of instantiated equation schemas

This file records the constructor alphabet used by a raw `Pattern` and proves
that matching and binding application cannot manufacture constructors outside
the concrete matched term or the authored schema.  The predicate is generic:
Cost later instantiates it with the declaration-derived non-principal
continuation signature.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open StructuralMorphism

mutual
  /-- Every constructor occurring in a pattern belongs to `allowed`. -/
  def ConstructorsWithin (allowed : String → Prop) : Pattern → Prop
    | .bvar _ | .fvar _ => True
    | .apply constructor arguments =>
        allowed constructor ∧ ConstructorListWithin allowed arguments
    | .lambda _ body => ConstructorsWithin allowed body
    | .multiLambda _ _ body => ConstructorsWithin allowed body
    | .subst body replacement =>
        ConstructorsWithin allowed body ∧
          ConstructorsWithin allowed replacement
    | .collection _ elements _ => ConstructorListWithin allowed elements

  /-- List companion to `ConstructorsWithin`. -/
  def ConstructorListWithin (allowed : String → Prop) : List Pattern → Prop
    | [] => True
    | pattern :: patterns =>
      ConstructorsWithin allowed pattern ∧
          ConstructorListWithin allowed patterns
end

mutual
  /-- Executable recognition of the constructor alphabet of one pattern. -/
  def checkConstructorsWithin (allowed : String → Bool) : Pattern → Bool
    | .bvar _ | .fvar _ => true
    | .apply constructor arguments =>
        allowed constructor && checkConstructorListWithin allowed arguments
    | .lambda _ body | .multiLambda _ _ body =>
        checkConstructorsWithin allowed body
    | .subst body replacement =>
        checkConstructorsWithin allowed body &&
          checkConstructorsWithin allowed replacement
    | .collection _ elements _ =>
        checkConstructorListWithin allowed elements

  /-- Executable pointwise constructor-alphabet recognition for a spine. -/
  def checkConstructorListWithin (allowed : String → Bool) :
      List Pattern → Bool
    | [] => true
    | pattern :: patterns =>
        checkConstructorsWithin allowed pattern &&
          checkConstructorListWithin allowed patterns
end

mutual
  /-- The executable pattern checker is exact for the proposition obtained
  by reading boolean membership as evidence. -/
  theorem checkConstructorsWithin_eq_true_iff (allowed : String → Bool)
      (pattern : Pattern) :
      checkConstructorsWithin allowed pattern = true ↔
        ConstructorsWithin (fun constructor => allowed constructor = true)
          pattern := by
    cases pattern with
    | bvar index => simp [checkConstructorsWithin, ConstructorsWithin]
    | fvar name => simp [checkConstructorsWithin, ConstructorsWithin]
    | apply constructor arguments =>
        simp only [checkConstructorsWithin, Bool.and_eq_true,
          ConstructorsWithin,
          checkConstructorListWithin_eq_true_iff allowed arguments]
    | lambda binder body =>
        exact checkConstructorsWithin_eq_true_iff allowed body
    | multiLambda arity binders body =>
        exact checkConstructorsWithin_eq_true_iff allowed body
    | subst body replacement =>
        simp only [checkConstructorsWithin, Bool.and_eq_true,
          ConstructorsWithin,
          checkConstructorsWithin_eq_true_iff allowed body,
          checkConstructorsWithin_eq_true_iff allowed replacement]
    | collection collectionType elements rest =>
        exact checkConstructorListWithin_eq_true_iff allowed elements

  /-- The executable spine checker is exact pointwise. -/
  theorem checkConstructorListWithin_eq_true_iff (allowed : String → Bool)
      (patterns : List Pattern) :
      checkConstructorListWithin allowed patterns = true ↔
        ConstructorListWithin (fun constructor => allowed constructor = true)
          patterns := by
    cases patterns with
    | nil =>
        simp [checkConstructorListWithin, ConstructorListWithin]
    | cons pattern patterns =>
        simp only [checkConstructorListWithin, Bool.and_eq_true,
          ConstructorListWithin,
          checkConstructorsWithin_eq_true_iff allowed pattern,
          checkConstructorListWithin_eq_true_iff allowed patterns]
end

/-- Specialization of the executable checker to a finite authored
constructor alphabet. -/
def checkConstructorsIn (allowed : List String) (pattern : Pattern) : Bool :=
  checkConstructorsWithin allowed.contains pattern

/-- Specialization of the executable spine checker to a finite authored
constructor alphabet. -/
def checkConstructorListIn (allowed : List String)
    (patterns : List Pattern) : Bool :=
  checkConstructorListWithin allowed.contains patterns

theorem checkConstructorsIn_eq_true_iff (allowed : List String)
    (pattern : Pattern) :
    checkConstructorsIn allowed pattern = true ↔
      ConstructorsWithin (· ∈ allowed) pattern := by
  simpa [checkConstructorsIn, List.contains_iff_mem] using
    checkConstructorsWithin_eq_true_iff allowed.contains pattern

theorem checkConstructorListIn_eq_true_iff (allowed : List String)
    (patterns : List Pattern) :
    checkConstructorListIn allowed patterns = true ↔
      ConstructorListWithin (· ∈ allowed) patterns := by
  simpa [checkConstructorListIn, List.contains_iff_mem] using
    checkConstructorListWithin_eq_true_iff allowed.contains patterns

namespace WellSorted

mutual
  /-- A typing derivation whose every authored constructor belongs to one
  selected declaration fragment.  Unlike raw `ConstructorsWithin`, this
  judgment records the constructor used by a bare collection representation,
  whose label is intentionally absent from `Pattern`. -/
  inductive HasTypeWithConstructors (language : LanguageDef)
      (allowed : String → Prop) (free : FreeTypeContext) :
      List TypeExpr → Pattern → TypeExpr → Prop where
    | bvar {bound : List TypeExpr} {index : Nat} {type : TypeExpr} :
        bound[index]? = some type →
        HasTypeWithConstructors language allowed free bound (.bvar index) type
    | fvar {bound : List TypeExpr} {name : String} {type : TypeExpr} :
        free name = some type →
        HasTypeWithConstructors language allowed free bound (.fvar name) type
    | constructor
        {bound : List TypeExpr} {rule : GrammarRule}
        {arguments : List Pattern} :
        allowed rule.label →
        rule ∈ language.terms →
        ¬ UsesBareCollection rule →
        ArgumentsHaveTypesWithConstructors language allowed free bound
          arguments rule.params →
        HasTypeWithConstructors language allowed free bound
          (.apply rule.label arguments) (.base rule.category)
    | lambda
        {bound : List TypeExpr} {binder : Option String} {body : Pattern}
        {domain codomain : TypeExpr} :
        HasTypeWithConstructors language allowed free (domain :: bound) body
          codomain →
        HasTypeWithConstructors language allowed free bound
          (.lambda binder body) (.arrow domain codomain)
    | multiLambda
        {bound : List TypeExpr} {arity : Nat} {binders : List String}
        {body : Pattern} {domain codomain : TypeExpr} :
        HasTypeWithConstructors language allowed free
          (List.replicate arity domain ++ bound) body codomain →
        HasTypeWithConstructors language allowed free bound
          (.multiLambda arity binders body)
          (.arrow (.multiBinder domain) codomain)
    | subst
        {bound : List TypeExpr} {body replacement : Pattern}
        {domain codomain : TypeExpr} :
        HasTypeWithConstructors language allowed free (domain :: bound) body
          codomain →
        HasTypeWithConstructors language allowed free bound replacement
          domain →
        HasTypeWithConstructors language allowed free bound
          (.subst body replacement) codomain
    | collection
        {bound : List TypeExpr} {collectionType : CollType}
        {elements : List Pattern} {rest : Option String}
        {elementType : TypeExpr} :
        ElementsHaveTypeWithConstructors language allowed free bound elements
          elementType →
        HasTypeWithConstructors language allowed free bound
          (.collection collectionType elements rest)
          (.collection collectionType elementType)
    | collectionConstructor
        {bound : List TypeExpr} {rule : GrammarRule}
        {parameterName : String} {collectionType : CollType}
        {elements : List Pattern} {rest : Option String}
        {elementType : TypeExpr} :
        allowed rule.label →
        rule ∈ language.terms →
        rule.params =
          [.simple parameterName (.collection collectionType elementType)] →
        ElementsHaveTypeWithConstructors language allowed free bound elements
          elementType →
        HasTypeWithConstructors language allowed free bound
          (.collection collectionType elements rest) (.base rule.category)

  /-- Ordered constructor arguments with the same declaration-fragment
  certificate. -/
  inductive ArgumentsHaveTypesWithConstructors (language : LanguageDef)
      (allowed : String → Prop) (free : FreeTypeContext) :
      List TypeExpr → List Pattern → List TermParam → Prop where
    | nil {bound : List TypeExpr} :
        ArgumentsHaveTypesWithConstructors language allowed free bound [] []
    | cons
        {argument : Pattern} {arguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr} :
        MatchesParameterRepresentation parameter argument →
        parameterType? parameter = some expected →
        HasTypeWithConstructors language allowed free bound argument expected →
        ArgumentsHaveTypesWithConstructors language allowed free bound
          arguments parameters →
        ArgumentsHaveTypesWithConstructors language allowed free bound
          (argument :: arguments) (parameter :: parameters)

  /-- Collection elements with the same declaration-fragment certificate. -/
  inductive ElementsHaveTypeWithConstructors (language : LanguageDef)
      (allowed : String → Prop) (free : FreeTypeContext) :
      List TypeExpr → List Pattern → TypeExpr → Prop where
    | nil (bound : List TypeExpr) (elementType : TypeExpr) :
        ElementsHaveTypeWithConstructors language allowed free bound []
          elementType
    | cons
        {element : Pattern} {elements : List Pattern}
        {elementType : TypeExpr} :
        HasTypeWithConstructors language allowed free bound element
          elementType →
        ElementsHaveTypeWithConstructors language allowed free bound elements
          elementType →
        ElementsHaveTypeWithConstructors language allowed free bound
          (element :: elements) elementType
end

mutual
  /-- Forget constructor-fragment evidence and recover ordinary typing. -/
  def HasTypeWithConstructors.toHasType
      {language : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : HasTypeWithConstructors language allowed free bound pattern type) :
      HasType language free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor _ membership notBare arguments =>
        exact .constructor membership notBare arguments.toArgumentsHaveTypes
    | lambda body => exact .lambda body.toHasType
    | multiLambda body => exact .multiLambda body.toHasType
    | subst body replacement =>
        exact .subst body.toHasType replacement.toHasType
    | collection elements =>
        exact .collection elements.toElementsHaveType
    | collectionConstructor _ membership shape elements =>
        exact .collectionConstructor membership shape
          elements.toElementsHaveType

  def ArgumentsHaveTypesWithConstructors.toArgumentsHaveTypes
      {language : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypesWithConstructors language allowed free bound
        arguments parameters) :
      ArgumentsHaveTypes language free bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argument arguments =>
        exact .cons representation parameterType argument.toHasType
          arguments.toArgumentsHaveTypes

  def ElementsHaveTypeWithConstructors.toElementsHaveType
      {language : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveTypeWithConstructors language allowed free bound
        elements elementType) :
      ElementsHaveType language free bound elements elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons element elements =>
        exact .cons element.toHasType elements.toElementsHaveType
end

/-- Invert a proof-relevant constructor-fragment typing judgment at an
application while retaining the selected declaration witness. -/
theorem hasTypeWithConstructors_apply_inversion
    {language : LanguageDef} {allowed : String → Prop}
    {free : FreeTypeContext} {bound : List TypeExpr}
    {label : String} {arguments : List Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors language allowed free bound
      (.apply label arguments) type) :
    ∃ rule, allowed rule.label ∧ rule ∈ language.terms ∧
      label = rule.label ∧ ¬ UsesBareCollection rule ∧
      type = .base rule.category ∧
      ArgumentsHaveTypesWithConstructors language allowed free bound
        arguments rule.params := by
  cases typed with
  | constructor allowedRule membership notBare argumentsTyped =>
      exact ⟨_, allowedRule, membership, rfl, notBare, rfl, argumentsTyped⟩

/-- Invert a proof-relevant constructor-fragment typing judgment at a
collection.  The second arm retains the otherwise syntax-invisible authored
declaration used for a bare collection. -/
theorem hasTypeWithConstructors_collection_inversion
    {language : LanguageDef} {allowed : String → Prop}
    {free : FreeTypeContext} {bound : List TypeExpr}
    {collectionType : CollType} {elements : List Pattern}
    {rest : Option String} {type : TypeExpr}
    (typed : HasTypeWithConstructors language allowed free bound
      (.collection collectionType elements rest) type) :
    (∃ elementType,
      type = .collection collectionType elementType ∧
      ElementsHaveTypeWithConstructors language allowed free bound elements
        elementType) ∨
    (∃ rule parameterName elementType,
      allowed rule.label ∧ rule ∈ language.terms ∧
      rule.params =
        [.simple parameterName (.collection collectionType elementType)] ∧
      type = .base rule.category ∧
      ElementsHaveTypeWithConstructors language allowed free bound elements
        elementType) := by
  cases typed with
  | collection elementsTyped =>
      exact Or.inl ⟨_, rfl, elementsTyped⟩
  | collectionConstructor allowedRule membership parameterShape elementsTyped =>
      exact Or.inr
        ⟨_, _, _, allowedRule, membership, parameterShape, rfl, elementsTyped⟩

/-- Invert proof-relevant typing of one unary binder. -/
theorem hasTypeWithConstructors_lambda_inversion
    {language : LanguageDef} {allowed : String → Prop}
    {free : FreeTypeContext} {bound : List TypeExpr}
    {binder : Option String} {body : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors language allowed free bound
      (.lambda binder body) type) :
    ∃ domain codomain, type = .arrow domain codomain ∧
      HasTypeWithConstructors language allowed free (domain :: bound) body
        codomain := by
  cases typed with
  | lambda bodyTyped => exact ⟨_, _, rfl, bodyTyped⟩

/-- Invert proof-relevant typing of one multi-binder. -/
theorem hasTypeWithConstructors_multiLambda_inversion
    {language : LanguageDef} {allowed : String → Prop}
    {free : FreeTypeContext} {bound : List TypeExpr}
    {arity : Nat} {binders : List String} {body : Pattern}
    {type : TypeExpr}
    (typed : HasTypeWithConstructors language allowed free bound
      (.multiLambda arity binders body) type) :
    ∃ domain codomain,
      type = .arrow (.multiBinder domain) codomain ∧
      HasTypeWithConstructors language allowed free
        (List.replicate arity domain ++ bound) body codomain := by
  cases typed with
  | multiLambda bodyTyped => exact ⟨_, _, rfl, bodyTyped⟩

/-- Proof-relevant typing transports across propositional equality of its
bound context and result type without discarding constructor witnesses. -/
theorem HasTypeWithConstructors.reindexBoundType
    {language : LanguageDef} {allowed : String → Prop}
    {free : FreeTypeContext} {sourceBound targetBound : List TypeExpr}
    {pattern : Pattern} {sourceType targetType : TypeExpr}
    (typed : HasTypeWithConstructors language allowed free sourceBound
      pattern sourceType)
    (boundEq : sourceBound = targetBound)
    (typeEq : sourceType = targetType) :
    HasTypeWithConstructors language allowed free targetBound pattern
      targetType := by
  subst targetBound
  subst targetType
  exact typed

/-- Concatenation preserves proof-relevant collection-element typing. -/
theorem ElementsHaveTypeWithConstructors.append
    {language : LanguageDef} {allowed : String → Prop}
    {free : FreeTypeContext} {bound : List TypeExpr}
    {left right : List Pattern} {elementType : TypeExpr}
    (leftTyped : ElementsHaveTypeWithConstructors language allowed free bound
      left elementType)
    (rightTyped : ElementsHaveTypeWithConstructors language allowed free bound
      right elementType) :
    ElementsHaveTypeWithConstructors language allowed free bound
      (left ++ right) elementType := by
  induction left with
  | nil =>
      cases leftTyped
      exact rightTyped
  | cons head tail inductionHypothesis =>
      cases leftTyped with
      | cons headTyped tailTyped =>
          exact .cons headTyped (inductionHypothesis tailTyped)

/-- Membership in a proof-relevant typed collection spine exposes the exact
typing derivation of that occurrence. -/
theorem ElementsHaveTypeWithConstructors.hasType_of_mem
    {language : LanguageDef} {allowed : String → Prop}
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (typed : ElementsHaveTypeWithConstructors language allowed free bound
      elements elementType)
    {element : Pattern} (membership : element ∈ elements) :
    HasTypeWithConstructors language allowed free bound element elementType := by
  induction elements with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      cases typed with
      | cons headTyped tailTyped =>
          rcases List.mem_cons.mp membership with rfl | inTail
          · exact headTyped
          · exact inductionHypothesis tailTyped inTail

mutual
  /-- Extending the declaration table preserves proof-relevant constructor
  support.  The selected constructor predicate is unchanged; only the table
  in which its witnessed declarations are looked up grows. -/
  theorem HasTypeWithConstructors.weakenTerms
      {sourceLanguage targetLanguage : LanguageDef}
      {allowed : String → Prop} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (includes : ∀ rule, rule ∈ sourceLanguage.terms →
        rule ∈ targetLanguage.terms)
      (typed : HasTypeWithConstructors sourceLanguage allowed free bound
        pattern type) :
      HasTypeWithConstructors targetLanguage allowed free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor allowed membership notBare arguments =>
        exact .constructor allowed (includes _ membership) notBare
          (arguments.weakenTerms includes)
    | lambda body => exact .lambda (body.weakenTerms includes)
    | multiLambda body => exact .multiLambda (body.weakenTerms includes)
    | subst body replacement =>
        exact .subst (body.weakenTerms includes)
          (replacement.weakenTerms includes)
    | collection elements => exact .collection (elements.weakenTerms includes)
    | collectionConstructor allowed membership shape elements =>
        exact .collectionConstructor allowed (includes _ membership) shape
          (elements.weakenTerms includes)

  theorem ArgumentsHaveTypesWithConstructors.weakenTerms
      {sourceLanguage targetLanguage : LanguageDef}
      {allowed : String → Prop} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (includes : ∀ rule, rule ∈ sourceLanguage.terms →
        rule ∈ targetLanguage.terms)
      (typed : ArgumentsHaveTypesWithConstructors sourceLanguage allowed free
        bound arguments parameters) :
      ArgumentsHaveTypesWithConstructors targetLanguage allowed free bound
        arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argument arguments =>
        exact .cons representation parameterType
          (argument.weakenTerms includes) (arguments.weakenTerms includes)

  theorem ElementsHaveTypeWithConstructors.weakenTerms
      {sourceLanguage targetLanguage : LanguageDef}
      {allowed : String → Prop} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (includes : ∀ rule, rule ∈ sourceLanguage.terms →
        rule ∈ targetLanguage.terms)
      (typed : ElementsHaveTypeWithConstructors sourceLanguage allowed free
        bound elements elementType) :
      ElementsHaveTypeWithConstructors targetLanguage allowed free bound
        elements elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons element elements =>
        exact .cons (element.weakenTerms includes)
          (elements.weakenTerms includes)
end

mutual
  /-- Typed constructor-fragment evidence implies the corresponding raw
  constructor support.  The reverse needs an explicit condition for bare
  collection constructors, proved below. -/
  theorem HasTypeWithConstructors.constructorsWithin
      {language : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : HasTypeWithConstructors language allowed free bound pattern type) :
      ConstructorsWithin allowed pattern := by
    cases typed with
    | bvar => trivial
    | fvar => trivial
    | constructor allowed _ _ arguments =>
        exact ⟨allowed, arguments.constructorListWithin⟩
    | lambda body => exact body.constructorsWithin
    | multiLambda body => exact body.constructorsWithin
    | subst body replacement =>
        exact ⟨body.constructorsWithin, replacement.constructorsWithin⟩
    | collection elements => exact elements.constructorListWithin
    | collectionConstructor _ _ _ elements =>
        exact elements.constructorListWithin

  theorem ArgumentsHaveTypesWithConstructors.constructorListWithin
      {language : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypesWithConstructors language allowed free bound
        arguments parameters) :
      ConstructorListWithin allowed arguments := by
    cases typed with
    | nil => trivial
    | cons _ _ argument arguments =>
        exact ⟨argument.constructorsWithin,
          arguments.constructorListWithin⟩

  theorem ElementsHaveTypeWithConstructors.constructorListWithin
      {language : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveTypeWithConstructors language allowed free bound
        elements elementType) :
      ConstructorListWithin allowed elements := by
    cases typed with
    | nil => trivial
    | cons element elements =>
        exact ⟨element.constructorsWithin, elements.constructorListWithin⟩
end

mutual
  /-- Ordinary typing plus raw constructor support lifts to the typed support
  judgment when every bare collection constructor belongs to the selected
  fragment. -/
  theorem HasType.withConstructors
      {language : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type)
      (supported : ConstructorsWithin allowed pattern)
      (bareAllowed : ∀ rule ∈ language.terms,
        UsesBareCollection rule → allowed rule.label) :
      HasTypeWithConstructors language allowed free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor membership notBare arguments =>
        exact .constructor supported.1 membership notBare
          (arguments.withConstructors supported.2 bareAllowed)
    | lambda body =>
        exact .lambda (body.withConstructors supported bareAllowed)
    | multiLambda body =>
        exact .multiLambda (body.withConstructors supported bareAllowed)
    | subst body replacement =>
        exact .subst
          (body.withConstructors supported.1 bareAllowed)
          (replacement.withConstructors supported.2 bareAllowed)
    | collection elements =>
        exact .collection
          (elements.withConstructors supported bareAllowed)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elements =>
        have bare : UsesBareCollection rule :=
          ⟨parameterName, collectionType, elementType, parameterShape⟩
        exact .collectionConstructor (bareAllowed rule membership bare)
          membership parameterShape
          (elements.withConstructors supported bareAllowed)

  theorem ArgumentsHaveTypes.withConstructors
      {language : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters)
      (supported : ConstructorListWithin allowed arguments)
      (bareAllowed : ∀ rule ∈ language.terms,
        UsesBareCollection rule → allowed rule.label) :
      ArgumentsHaveTypesWithConstructors language allowed free bound arguments
        parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argument arguments =>
        exact .cons representation parameterType
          (argument.withConstructors supported.1 bareAllowed)
          (arguments.withConstructors supported.2 bareAllowed)

  theorem ElementsHaveType.withConstructors
      {language : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType)
      (supported : ConstructorListWithin allowed elements)
      (bareAllowed : ∀ rule ∈ language.terms,
        UsesBareCollection rule → allowed rule.label) :
      ElementsHaveTypeWithConstructors language allowed free bound elements
        elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons element elements =>
        exact .cons
          (element.withConstructors supported.1 bareAllowed)
          (elements.withConstructors supported.2 bareAllowed)
end

end WellSorted

@[simp] theorem constructorsWithin_bvar (allowed : String → Prop) (index : Nat) :
    ConstructorsWithin allowed (.bvar index) :=
  trivial

@[simp] theorem constructorsWithin_fvar (allowed : String → Prop) (name : String) :
    ConstructorsWithin allowed (.fvar name) :=
  trivial

@[simp] theorem constructorsWithin_apply (allowed : String → Prop)
    (constructor : String) (arguments : List Pattern) :
    ConstructorsWithin allowed (.apply constructor arguments) ↔
      allowed constructor ∧ ConstructorListWithin allowed arguments :=
  Iff.rfl

@[simp] theorem constructorsWithin_lambda (allowed : String → Prop)
    (binder : Option String) (body : Pattern) :
    ConstructorsWithin allowed (.lambda binder body) ↔
      ConstructorsWithin allowed body :=
  Iff.rfl

@[simp] theorem constructorsWithin_multiLambda (allowed : String → Prop)
    (arity : Nat) (binders : List String) (body : Pattern) :
    ConstructorsWithin allowed (.multiLambda arity binders body) ↔
      ConstructorsWithin allowed body :=
  Iff.rfl

@[simp] theorem constructorsWithin_subst (allowed : String → Prop)
    (body replacement : Pattern) :
    ConstructorsWithin allowed (.subst body replacement) ↔
      ConstructorsWithin allowed body ∧
        ConstructorsWithin allowed replacement :=
  Iff.rfl

@[simp] theorem constructorsWithin_collection (allowed : String → Prop)
    (collectionType : CollType) (elements : List Pattern)
    (rest : Option String) :
    ConstructorsWithin allowed (.collection collectionType elements rest) ↔
      ConstructorListWithin allowed elements :=
  Iff.rfl

@[simp] theorem constructorListWithin_nil (allowed : String → Prop) :
    ConstructorListWithin allowed [] :=
  trivial

@[simp] theorem constructorListWithin_cons (allowed : String → Prop)
    (pattern : Pattern) (patterns : List Pattern) :
    ConstructorListWithin allowed (pattern :: patterns) ↔
      ConstructorsWithin allowed pattern ∧
        ConstructorListWithin allowed patterns :=
  Iff.rfl

/-- List support is exactly pointwise pattern support. -/
theorem constructorListWithin_iff_forall {allowed : String → Prop}
    (patterns : List Pattern) :
    ConstructorListWithin allowed patterns ↔
      ∀ pattern ∈ patterns, ConstructorsWithin allowed pattern := by
  induction patterns with
  | nil => simp
  | cons pattern patterns inductionHypothesis =>
      simp only [constructorListWithin_cons, List.mem_cons,
        forall_eq_or_imp, inductionHypothesis]

/-- Constructor support is invariant under permutation of a spine. -/
theorem ConstructorListWithin.perm {allowed : String → Prop}
    {first second : List Pattern} (permutation : first.Perm second) :
    ConstructorListWithin allowed first ↔
      ConstructorListWithin allowed second := by
  simp only [constructorListWithin_iff_forall]
  constructor
  · intro supported pattern membership
    exact supported pattern (permutation.mem_iff.mpr membership)
  · intro supported pattern membership
    exact supported pattern (permutation.mem_iff.mp membership)

/-- Membership extracts the pointwise constructor-support judgment. -/
theorem ConstructorListWithin.of_mem {allowed : String → Prop}
    {patterns : List Pattern} (supported : ConstructorListWithin allowed patterns)
    {pattern : Pattern} (membership : pattern ∈ patterns) :
    ConstructorsWithin allowed pattern := by
  induction patterns with
  | nil => cases membership
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact supported.1
      · exact inductionHypothesis supported.2 membership

/-- Removing one collection occurrence preserves constructor support. -/
theorem ConstructorListWithin.eraseIdx {allowed : String → Prop}
    {patterns : List Pattern} (supported : ConstructorListWithin allowed patterns)
    (index : Nat) : ConstructorListWithin allowed (patterns.eraseIdx index) := by
  induction patterns generalizing index with
  | nil => trivial
  | cons pattern patterns inductionHypothesis =>
      cases index with
      | zero => exact supported.2
      | succ index =>
          exact ⟨supported.1, inductionHypothesis supported.2 index⟩

/-- Concatenating two supported spines preserves support. -/
theorem ConstructorListWithin.append {allowed : String → Prop}
    {first second : List Pattern}
    (firstSupported : ConstructorListWithin allowed first)
    (secondSupported : ConstructorListWithin allowed second) :
    ConstructorListWithin allowed (first ++ second) := by
  induction first generalizing second with
  | nil => exact secondSupported
  | cons pattern patterns inductionHypothesis =>
      exact ⟨firstSupported.1,
        inductionHypothesis firstSupported.2 secondSupported⟩

/-- Mapping a spine preserves constructor support when every mapped member is
supported. -/
theorem ConstructorListWithin.map {allowed : String → Prop}
    {patterns : List Pattern} {f : Pattern → Pattern}
    (supported : ConstructorListWithin allowed patterns)
    (mappedSupported : ∀ pattern ∈ patterns,
      ConstructorsWithin allowed (f pattern)) :
    ConstructorListWithin allowed (patterns.map f) := by
  induction patterns with
  | nil => trivial
  | cons pattern patterns inductionHypothesis =>
      exact ⟨mappedSupported pattern (by simp),
        inductionHypothesis supported.2
          (fun other membership => mappedSupported other (by simp [membership]))⟩

/-- Constructor support is covariant in its admitted alphabet. -/
theorem ConstructorsWithin.mono
    {narrow broad : String → Prop} (includes : ∀ label, narrow label → broad label)
    {pattern : Pattern} (supported : ConstructorsWithin narrow pattern) :
    ConstructorsWithin broad pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => trivial
  | hfvar name => trivial
  | happly constructor arguments inductionHypothesis =>
      refine ⟨includes constructor supported.1, ?_⟩
      rw [constructorListWithin_iff_forall]
      intro argument membership
      exact inductionHypothesis argument membership
        (supported.2.of_mem membership)
  | hlambda binder body inductionHypothesis =>
      exact inductionHypothesis supported
  | hmultiLambda arity binders body inductionHypothesis =>
      exact inductionHypothesis supported
  | hsubst body replacement bodyInduction replacementInduction =>
      exact ⟨bodyInduction supported.1, replacementInduction supported.2⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      change ConstructorListWithin broad elements
      rw [constructorListWithin_iff_forall]
      intro element membership
      exact inductionHypothesis element membership
        (supported.of_mem membership)

/-- List companion to `ConstructorsWithin.mono`. -/
theorem ConstructorListWithin.mono
    {narrow broad : String → Prop} (includes : ∀ label, narrow label → broad label)
    {patterns : List Pattern} (supported : ConstructorListWithin narrow patterns) :
    ConstructorListWithin broad patterns := by
  induction patterns with
  | nil => trivial
  | cons head tail inductionHypothesis =>
      exact ⟨supported.1.mono includes, inductionHypothesis supported.2⟩

mutual
  /-- A presentation-symbol action preserves constructor support whenever it
  sends every allowed source label into the target fragment. -/
  theorem constructorsWithin_mapPattern
      {sourceAllowed targetAllowed : String → Prop}
      (symbols : LanguageDefSymbolMap)
      (mapsAllowed : ∀ constructor,
        sourceAllowed constructor →
          targetAllowed (symbols.constructor constructor))
      {pattern : Pattern}
      (supported : ConstructorsWithin sourceAllowed pattern) :
      ConstructorsWithin targetAllowed (mapPattern symbols pattern) := by
    induction pattern using Pattern.inductionOn with
    | hbvar index => trivial
    | hfvar name => trivial
    | happly constructor arguments inductionHypothesis =>
        simpa [mapPattern, mapPatternList_eq_map] using
          And.intro (mapsAllowed constructor supported.1)
            (constructorListWithin_mapPattern symbols supported.2
              inductionHypothesis)
    | hlambda binder body inductionHypothesis =>
        exact inductionHypothesis supported
    | hmultiLambda arity binders body inductionHypothesis =>
        exact inductionHypothesis supported
    | hsubst body replacement bodyInduction replacementInduction =>
        exact ⟨bodyInduction supported.1, replacementInduction supported.2⟩
    | hcollection collectionType elements rest inductionHypothesis =>
        simpa [mapPattern, mapPatternList_eq_map] using
          constructorListWithin_mapPattern symbols supported
            inductionHypothesis

  /-- List companion to `constructorsWithin_mapPattern`. -/
  theorem constructorListWithin_mapPattern
      {sourceAllowed targetAllowed : String → Prop}
      (symbols : LanguageDefSymbolMap)
      {patterns : List Pattern}
      (supported : ConstructorListWithin sourceAllowed patterns)
      (inductionHypothesis : ∀ pattern ∈ patterns,
        ConstructorsWithin sourceAllowed pattern →
          ConstructorsWithin targetAllowed (mapPattern symbols pattern)) :
      ConstructorListWithin targetAllowed
        (patterns.map (mapPattern symbols)) := by
    rw [constructorListWithin_iff_forall]
    intro mapped membership
    rcases List.mem_map.mp membership with ⟨pattern, sourceMembership, rfl⟩
    exact inductionHypothesis pattern sourceMembership
      (supported.of_mem sourceMembership)
end

/-- De Bruijn lifting changes no constructor label. -/
theorem constructorsWithin_liftBVars {allowed : String → Prop}
    {pattern : Pattern} (supported : ConstructorsWithin allowed pattern)
    (cutoff shift : Nat) :
    ConstructorsWithin allowed (liftBVars cutoff shift pattern) := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      simp only [liftBVars]
      split <;> exact trivial
  | hfvar name => simp [liftBVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [liftBVars, constructorsWithin_apply]
      exact ⟨supported.1, supported.2.map fun argument membership =>
        inductionHypothesis argument membership
          (supported.2.of_mem membership) cutoff⟩
  | hlambda binder body inductionHypothesis =>
      simpa only [liftBVars, constructorsWithin_lambda] using
        inductionHypothesis supported (cutoff + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa only [liftBVars, constructorsWithin_multiLambda] using
        inductionHypothesis supported (cutoff + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simpa only [liftBVars, constructorsWithin_subst] using
        And.intro (bodyInduction supported.1 (cutoff + 1))
          (replacementInduction supported.2 cutoff)
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [liftBVars, constructorsWithin_collection]
      exact supported.map fun element membership =>
        inductionHypothesis element membership
          (supported.of_mem membership) cutoff

/-- Instantiating a locally nameless binder combines only constructors from
the body and replacement. -/
theorem constructorsWithin_instantiateBVarAt {allowed : String → Prop}
    {body replacement : Pattern}
    (bodySupported : ConstructorsWithin allowed body)
    (replacementSupported : ConstructorsWithin allowed replacement)
    (depth : Nat) :
    ConstructorsWithin allowed (instantiateBVarAt depth replacement body) := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      by_cases below : index < depth
      · simp [instantiateBVarAt, below]
      · by_cases equal : index = depth
        · subst index
          simpa [instantiateBVarAt] using
            constructorsWithin_liftBVars replacementSupported 0 depth
        · simp [instantiateBVarAt, below, equal]
  | hfvar name => simp [instantiateBVarAt]
  | happly constructor arguments inductionHypothesis =>
      simp only [instantiateBVarAt, constructorsWithin_apply]
      exact ⟨bodySupported.1, bodySupported.2.map fun argument membership =>
        inductionHypothesis argument membership
          (bodySupported.2.of_mem membership) depth⟩
  | hlambda binder nestedBody inductionHypothesis =>
      simpa only [instantiateBVarAt, constructorsWithin_lambda] using
        inductionHypothesis bodySupported (depth + 1)
  | hmultiLambda arity binders nestedBody inductionHypothesis =>
      simpa only [instantiateBVarAt, constructorsWithin_multiLambda] using
        inductionHypothesis bodySupported (depth + arity)
  | hsubst nestedBody nestedReplacement bodyInduction replacementInduction =>
      simpa only [instantiateBVarAt, constructorsWithin_subst] using
        And.intro (bodyInduction bodySupported.1 (depth + 1))
          (replacementInduction bodySupported.2 depth)
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [instantiateBVarAt, constructorsWithin_collection]
      exact bodySupported.map fun element membership =>
        inductionHypothesis element membership
          (bodySupported.of_mem membership) depth

theorem constructorsWithin_instantiateBVar {allowed : String → Prop}
    {body replacement : Pattern}
    (bodySupported : ConstructorsWithin allowed body)
    (replacementSupported : ConstructorsWithin allowed replacement) :
    ConstructorsWithin allowed (instantiateBVar replacement body) :=
  constructorsWithin_instantiateBVarAt bodySupported replacementSupported 0

/-- Every value stored in a matcher environment satisfies the constructor
support predicate. -/
def BindingsWithin (allowed : String → Prop) (bindings : Bindings) : Prop :=
  ∀ entry ∈ bindings, ConstructorsWithin allowed entry.2

/-- Successful binding merge preserves a pointwise support invariant. -/
theorem bindingsWithin_merge {allowed : String → Prop}
    {first second merged : Bindings}
    (firstSupported : BindingsWithin allowed first)
    (secondSupported : BindingsWithin allowed second)
    (merge : mergeBindings first second = some merged) :
    BindingsWithin allowed merged := by
  unfold mergeBindings at merge
  induction second generalizing first with
  | nil =>
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at merge
      subst merged
      exact firstSupported
  | cons entry entries inductionHypothesis =>
      rcases entry with ⟨name, value⟩
      simp only [List.foldlM_cons] at merge
      dsimp only [Bind.bind, Option.bind] at merge
      cases found : first.find? (fun pair => pair.1 == name) with
      | none =>
          simp only [found] at merge
          have accumulatorSupported :
              BindingsWithin allowed ((name, value) :: first) := by
            intro pair membership
            rcases List.mem_cons.mp membership with rfl | membership
            · exact secondSupported (name, value) (by simp)
            · exact firstSupported pair membership
          have remainingSupported : BindingsWithin allowed entries := by
            intro pair membership
            exact secondSupported pair (by simp [membership])
          exact inductionHypothesis accumulatorSupported remainingSupported merge
      | some pair =>
          rcases pair with ⟨existingName, existingValue⟩
          simp only [found] at merge
          cases equal : existingValue == value
          · simp only [equal] at merge
            simp at merge
          · simp only [equal] at merge
            exact inductionHypothesis firstSupported
              (fun pair membership => secondSupported pair (by simp [membership]))
              merge

mutual
  /-- Relational matching binds only constructor-supported subterms of the
  concrete term. -/
  theorem matchRel_bindingsWithin {allowed : String → Prop}
      {schema term : Pattern} {bindings : Bindings}
      (derivation : MatchRel schema term bindings)
      (termSupported : ConstructorsWithin allowed term) :
      BindingsWithin allowed bindings := by
    cases derivation with
    | fvar =>
        intro entry membership
        simp only [List.mem_singleton] at membership
        subst entry
        exact termSupported
    | bvar =>
        intro entry membership
        simp at membership
    | apply arguments _ =>
        exact matchArgsRel_bindingsWithin arguments termSupported.2
    | lambda body =>
        exact matchRel_bindingsWithin body termSupported
    | multiLambda body =>
        exact matchRel_bindingsWithin body termSupported
    | collection bag =>
        exact matchBagRel_bindingsWithin bag termSupported
    | subst body replacement merge =>
        exact bindingsWithin_merge
          (matchRel_bindingsWithin body termSupported.1)
          (matchRel_bindingsWithin replacement termSupported.2) merge

  /-- Ordered argument matching binds only supported subterms. -/
  theorem matchArgsRel_bindingsWithin {allowed : String → Prop}
      {schemas terms : List Pattern} {bindings : Bindings}
      (derivation : MatchArgsRel schemas terms bindings)
      (termsSupported : ConstructorListWithin allowed terms) :
      BindingsWithin allowed bindings := by
    cases derivation with
    | nil =>
        intro entry membership
        simp at membership
    | cons head tail merge =>
        exact bindingsWithin_merge
          (matchRel_bindingsWithin head termsSupported.1)
          (matchArgsRel_bindingsWithin tail termsSupported.2) merge

  /-- Multiset matching, including an open rest capture, binds only supported
  subterms. -/
  theorem matchBagRel_bindingsWithin {allowed : String → Prop}
      {schemas : List Pattern} {rest : Option String}
      {collectionType : CollType} {terms : List Pattern}
      {bindings : Bindings}
      (derivation : MatchBagRel schemas rest collectionType terms bindings)
      (termsSupported : ConstructorListWithin allowed terms) :
      BindingsWithin allowed bindings := by
    cases derivation with
    | nilNoRest =>
        intro entry membership
        simp at membership
    | nilRest =>
        intro entry membership
        simp only [List.mem_singleton] at membership
        subst entry
        exact termsSupported
    | cons index indexBound head tail merge =>
        have selectedSupported : ConstructorsWithin allowed terms[index] :=
          termsSupported.of_mem (List.getElem_mem indexBound)
        exact bindingsWithin_merge
          (matchRel_bindingsWithin head selectedSupported)
          (matchBagRel_bindingsWithin tail
            (ConstructorListWithin.eraseIdx termsSupported index)) merge
end

/-- Applying a supported matcher environment to a supported schema preserves
constructor support.  The explicit-substitution case uses the proved
locally-nameless instantiation lemma above. -/
theorem constructorsWithin_applyBindings {allowed : String → Prop}
    {schema : Pattern} (schemaSupported : ConstructorsWithin allowed schema)
    {bindings : Bindings} (bindingsSupported : BindingsWithin allowed bindings) :
    ConstructorsWithin allowed (applyBindings bindings schema) := by
  induction schema using Pattern.inductionOn with
  | hbvar index => simp [applyBindings]
  | hfvar name =>
      cases found : bindings.find? (fun entry => entry.1 == name) with
      | none => simp [applyBindings, found]
      | some entry =>
          have membership := List.mem_of_find?_eq_some found
          simpa [applyBindings, found] using
            bindingsSupported entry membership
  | happly constructor arguments inductionHypothesis =>
      simp only [applyBindings, constructorsWithin_apply]
      exact ⟨schemaSupported.1, schemaSupported.2.map fun argument membership =>
        inductionHypothesis argument membership
          (schemaSupported.2.of_mem membership)⟩
  | hlambda binder body inductionHypothesis =>
      simpa [applyBindings] using inductionHypothesis schemaSupported
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [applyBindings] using inductionHypothesis schemaSupported
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [applyBindings]
      exact constructorsWithin_instantiateBVar
        (bodyInduction schemaSupported.1)
        (replacementInduction schemaSupported.2)
  | hcollection collectionType elements rest inductionHypothesis =>
      have mappedSupported : ConstructorListWithin allowed
          (elements.map (applyBindings bindings)) := by
        exact schemaSupported.map fun element membership =>
          inductionHypothesis element membership
            (schemaSupported.of_mem membership)
      cases rest with
      | none => simpa [applyBindings] using mappedSupported
      | some restName =>
          cases found : bindings.find? (fun entry => entry.1 == restName) with
          | none => simpa [applyBindings, found] using mappedSupported
          | some entry =>
              have entrySupported :=
                bindingsSupported entry (List.mem_of_find?_eq_some found)
              rcases entry with ⟨entryName, value⟩
              cases value with
              | collection boundType restElements boundRest =>
                  cases boundRest with
                  | none =>
                      by_cases same : boundType == collectionType
                      · simpa [applyBindings, found, same] using
                          mappedSupported.append entrySupported
                      · simpa [applyBindings, found, same] using mappedSupported
                  | some nestedRest =>
                      simpa [applyBindings, found] using mappedSupported
              | bvar index => simpa [applyBindings, found] using mappedSupported
              | fvar name => simpa [applyBindings, found] using mappedSupported
              | apply constructor arguments =>
                  simpa [applyBindings, found] using mappedSupported
              | lambda binder body =>
                  simpa [applyBindings, found] using mappedSupported
              | multiLambda arity binders body =>
                  simpa [applyBindings, found] using mappedSupported
              | subst body replacement =>
                  simpa [applyBindings, found] using mappedSupported

end Mettapedia.GSLT.LanguageDef
