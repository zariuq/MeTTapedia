import Mettapedia.GSLT.LanguageDef.RestAwareTyping
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Executable checking of rest-aware authored schemas

This checker shares the old constructor and binder interpretation. At every
collection it checks the rest against the same element type used to check its
elements. For an explicit substitution, it searches the finitely declared
base sorts for the eliminated variable's type. Compound substitution domains
require a richer candidate supply and are not claimed complete here.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

/-- Executable form of the rest's contextual type premise. -/
def checkRestHasType (free : FreeTypeContext) (kind : CollType)
    (elementType : TypeExpr) : Option String → Bool
  | none => true
  | some name => free name == some (.collection kind elementType)

theorem checkRestHasType_sound {free : FreeTypeContext} {kind : CollType}
    {elementType : TypeExpr} {rest : Option String}
    (checked : checkRestHasType free kind elementType rest = true) :
    RestHasType free kind elementType rest := by
  cases rest with
  | none => trivial
  | some name =>
      simpa [checkRestHasType, RestHasType] using checked

mutual
  /-- Check a raw schema against one expected type and exact contexts. -/
  def checkSchemaHasType (language : LanguageDef) (free : FreeTypeContext)
      (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) : Bool :=
    match pattern with
    | .bvar index => bound[index]? == some expected
    | .fvar name => free name == some expected
    | .apply constructor arguments =>
        language.terms.any fun rule =>
          rule.label == constructor && expected == .base rule.category &&
            !usesBareCollection? rule &&
            checkSchemaArguments language free bound arguments rule.params
    | .lambda _ body =>
        match expected with
        | .arrow domain codomain =>
            checkSchemaHasType language free (domain :: bound) body codomain
        | _ => false
    | .multiLambda arity _ body =>
        match expected with
        | .arrow (.multiBinder domain) codomain =>
            checkSchemaHasType language free
              (List.replicate arity domain ++ bound) body codomain
        | _ => false
    | .subst body replacement =>
        language.types.any fun declaration =>
          checkSchemaHasType language free
              (.base declaration.name :: bound) body expected &&
            checkSchemaHasType language free bound replacement
              (.base declaration.name)
    | .collection kind elements rest =>
        let direct :=
          match expected with
          | .collection actual elementType =>
              actual == kind &&
                checkSchemaElements language free bound elements elementType &&
                checkRestHasType free kind elementType rest
          | _ => false
        let authored := language.terms.any fun rule =>
          match bareCollectionElementType? rule kind expected with
          | some elementType =>
              checkSchemaElements language free bound elements elementType &&
                checkRestHasType free kind elementType rest
          | none => false
        direct || authored

  /-- Check an ordered constructor argument spine. -/
  def checkSchemaArguments (language : LanguageDef) (free : FreeTypeContext)
      (bound : List TypeExpr) : List Pattern → List TermParam → Bool
    | [], [] => true
    | argument :: arguments, parameter :: parameters =>
        match parameterType? parameter with
        | some expected =>
            matchesParameterRepresentation? parameter argument &&
              checkSchemaHasType language free bound argument expected &&
              checkSchemaArguments language free bound arguments parameters
        | none => false
    | _, _ => false

  /-- Check every element at the same declared element type. -/
  def checkSchemaElements (language : LanguageDef) (free : FreeTypeContext)
      (bound : List TypeExpr) : List Pattern → TypeExpr → Bool
    | [], _ => true
    | element :: elements, elementType =>
        checkSchemaHasType language free bound element elementType &&
          checkSchemaElements language free bound elements elementType
end

theorem checkSchemaArguments_sound_of
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (argumentSound : ∀ argument ∈ arguments, ∀ expected,
      checkSchemaHasType language free bound argument expected = true →
        HasType language free bound argument expected)
    (checked : checkSchemaArguments language free bound arguments parameters = true) :
    ArgumentsHaveTypes language free bound arguments parameters := by
  induction arguments generalizing parameters with
  | nil =>
      cases parameters with
      | nil => exact .nil
      | cons parameter parameters => simp [checkSchemaArguments] at checked
  | cons argument arguments inductionHypothesis =>
      cases parameters with
      | nil => simp [checkSchemaArguments] at checked
      | cons parameter parameters =>
          cases parameterTypeEquation : parameterType? parameter with
          | none => simp [checkSchemaArguments, parameterTypeEquation] at checked
          | some expected =>
              simp only [checkSchemaArguments, parameterTypeEquation,
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

theorem checkSchemaElements_sound_of
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (elementSound : ∀ element ∈ elements,
      checkSchemaHasType language free bound element elementType = true →
        HasType language free bound element elementType)
    (checked : checkSchemaElements language free bound elements elementType = true) :
    ElementsHaveType language free bound elements elementType := by
  induction elements with
  | nil => exact .nil bound elementType
  | cons element elements inductionHypothesis =>
      simp only [checkSchemaElements, Bool.and_eq_true] at checked
      exact .cons
        (elementSound element (by simp) checked.1)
        (inductionHypothesis
          (fun other membership otherChecked =>
            elementSound other (by simp [membership]) otherChecked)
          checked.2)

/-- A successful executable schema check produces the full rest-aware
declarative derivation. -/
theorem checkSchemaHasType_sound
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (checked : checkSchemaHasType language free bound pattern expected = true) :
    HasType language free bound pattern expected := by
  induction pattern using Pattern.inductionOn generalizing bound expected with
  | hbvar index =>
      simp only [checkSchemaHasType, beq_iff_eq] at checked
      exact .bvar checked
  | hfvar name =>
      simp only [checkSchemaHasType, beq_iff_eq] at checked
      exact .fvar checked
  | happly constructor arguments inductionHypothesis =>
      simp only [checkSchemaHasType, List.any_eq_true, Bool.and_eq_true,
        beq_iff_eq, Bool.not_eq_true'] at checked
      obtain ⟨rule, ruleMember,
        ⟨⟨⟨labelEquality, expectedEquality⟩, notBare⟩,
          argumentsChecked⟩⟩ := checked
      subst constructor
      subst expected
      exact .constructor ruleMember
        (by
          intro bare
          have bareChecked := (usesBareCollection?_eq_true_iff rule).mpr bare
          rw [bareChecked] at notBare
          contradiction)
        (checkSchemaArguments_sound_of
          (fun argument membership argumentExpected argumentChecked =>
            inductionHypothesis argument membership argumentChecked)
          argumentsChecked)
  | hlambda binder body inductionHypothesis =>
      cases expected with
      | arrow domain codomain => exact .lambda (inductionHypothesis checked)
      | base sort => simp [checkSchemaHasType] at checked
      | multiBinder type => simp [checkSchemaHasType] at checked
      | collection kind elementType => simp [checkSchemaHasType] at checked
  | hmultiLambda arity binders body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder binderType =>
              exact .multiLambda (inductionHypothesis checked)
          | base sort => simp [checkSchemaHasType] at checked
          | arrow first second => simp [checkSchemaHasType] at checked
          | collection kind elementType => simp [checkSchemaHasType] at checked
      | base sort => simp [checkSchemaHasType] at checked
      | multiBinder type => simp [checkSchemaHasType] at checked
      | collection kind elementType => simp [checkSchemaHasType] at checked
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [checkSchemaHasType, List.any_eq_true,
        Bool.and_eq_true] at checked
      obtain ⟨declaration, _, bodyChecked, replacementChecked⟩ := checked
      exact .subst (bodyHypothesis bodyChecked)
        (replacementHypothesis replacementChecked)
  | hcollection kind elements rest inductionHypothesis =>
      simp only [checkSchemaHasType, Bool.or_eq_true, List.any_eq_true] at checked
      rcases checked with direct | authored
      · cases expected with
        | collection actual elementType =>
            simp only [Bool.and_eq_true, beq_iff_eq] at direct
            rcases direct with ⟨⟨actualEquality, elementsChecked⟩, restChecked⟩
            subst actual
            exact .collection
              (checkSchemaElements_sound_of
                (fun element membership elementChecked =>
                  inductionHypothesis element membership elementChecked)
                elementsChecked)
              (checkRestHasType_sound restChecked)
        | base sort => simp at direct
        | arrow domain codomain => simp at direct
        | multiBinder type => simp at direct
      · obtain ⟨rule, ruleMember, ruleChecked⟩ := authored
        generalize elementTypeEquation :
          bareCollectionElementType? rule kind expected = result at ruleChecked
        cases result with
        | none => simp at ruleChecked
        | some elementType =>
            rw [bareCollectionElementType?_eq_some_iff] at elementTypeEquation
            rcases elementTypeEquation with
              ⟨expectedEquality, parameterName, parameterShape⟩
            subst expected
            simp only [Bool.and_eq_true] at ruleChecked
            exact .collectionConstructor ruleMember parameterShape
              (checkSchemaElements_sound_of
                (fun element membership elementChecked =>
                  inductionHypothesis element membership elementChecked)
                ruleChecked.1)
              (checkRestHasType_sound ruleChecked.2)

/-- Search the authored base sorts for a common type of the two sides of a
rewrite. This is sound and partial: substitutions whose eliminated variable
has a compound type are outside the current finite candidate set. -/
def checkRewriteHasType (language : LanguageDef) (rewrite : RewriteRule) : Bool :=
  language.types.any fun declaration =>
    checkSchemaHasType language
        (FreeTypeContext.ofList rewrite.typeContext) []
        rewrite.left (.base declaration.name) &&
      checkSchemaHasType language
        (FreeTypeContext.ofList rewrite.typeContext) []
        rewrite.right (.base declaration.name)

theorem checkRewriteHasType_sound
    {language : LanguageDef} {rewrite : RewriteRule}
    (checked : checkRewriteHasType language rewrite = true) :
    RewriteHasType language rewrite := by
  simp only [checkRewriteHasType, List.any_eq_true, Bool.and_eq_true] at checked
  obtain ⟨declaration, _, leftChecked, rightChecked⟩ := checked
  exact ⟨.base declaration.name,
    checkSchemaHasType_sound leftChecked,
    checkSchemaHasType_sound rightChecked⟩

def checkEquationHasType (language : LanguageDef) (equation : Equation) : Bool :=
  language.types.any fun declaration =>
    checkSchemaHasType language
        (FreeTypeContext.ofList equation.typeContext) []
        equation.left (.base declaration.name) &&
      checkSchemaHasType language
        (FreeTypeContext.ofList equation.typeContext) []
        equation.right (.base declaration.name)

theorem checkEquationHasType_sound
    {language : LanguageDef} {equation : Equation}
    (checked : checkEquationHasType language equation = true) :
    EquationHasType language equation := by
  simp only [checkEquationHasType, List.any_eq_true, Bool.and_eq_true] at checked
  obtain ⟨declaration, _, leftChecked, rightChecked⟩ := checked
  exact ⟨.base declaration.name,
    checkSchemaHasType_sound leftChecked,
    checkSchemaHasType_sound rightChecked⟩

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
