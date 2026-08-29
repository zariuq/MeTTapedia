import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Contextual result families: binders and first-order application

A contextual modal type may depend on a finite ordered row of rely values.
There are two useful views of that dependency:

* an intensional curried body under one binder per rely value;
* a first-order application node carrying the family and its arguments.

The first view is the authored mathematical syntax.  The second is the stable
checker and compiler wire.  This module makes their boundary explicit.

The exact-depth rule checker explains why this boundary matters.  Unary
explicit substitution is directly representable, but naively nesting the same
encoding makes an earlier argument occur below later substitution binders.
Reusing that argument elsewhere at top level then gives it two occurrence
depths, which an exact schema must reject.  A first-order application node
keeps the family and every argument at depth zero, while a separate denotation
records the curried meaning.
-/

namespace Mettapedia.OSLF.Framework.ContextualFamilyApplication

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.InferenceChecker

private abbrev schemaOccurrences : RuleSchema → List (String × Nat) :=
  Mettapedia.GSLT.LanguageDef.InferenceChecker.RuleSchema.occurrences

private abbrev schemaLocallyValid : RuleSchema → Bool :=
  Mettapedia.GSLT.LanguageDef.InferenceChecker.RuleSchema.isLocallyValid

/-! ## Intensional curried families -/

/-- Canonical nested unary abstraction.  The first argument is the outermost
binder, so a body of arity `n` refers to it at index `n - 1`. -/
def curryLambdas : Nat → Pattern → Pattern
  | 0, body => body
  | arity + 1, body => .lambda none (curryLambdas arity body)

/-- Instantiate a curried body with arguments in source order.  Reversing the
argument row is the de Bruijn content: the last source argument is index zero,
while the first source argument is the outermost binder. -/
def instantiateCurried (arguments : List Pattern) (body : Pattern) : Pattern :=
  arguments.reverse.foldl (fun current argument =>
    instantiateBVar argument current) body

/-- The semantic relation between a curried family, its ordered arguments,
and the result of applying it. -/
def Denotes (family : Pattern) (arguments : List Pattern)
    (result : Pattern) : Prop :=
  ∃ body,
    family = curryLambdas arguments.length body ∧
      result = instantiateCurried arguments body

/-! ## Structural explicit substitution and its depth obstruction -/

/-- Naive left-associated explicit substitution.  This is faithful for one
argument.  With two or more arguments, earlier replacements lie under the
binders introduced by later `.subst` nodes. -/
def nestedExplicitSubstitution : Pattern → List Pattern → Pattern
  | body, [] => body
  | body, argument :: arguments =>
      nestedExplicitSubstitution (.subst body argument) arguments

@[simp] theorem nestedExplicitSubstitution_nil (body : Pattern) :
    nestedExplicitSubstitution body [] = body :=
  rfl

@[simp] theorem nestedExplicitSubstitution_singleton
    (body argument : Pattern) :
    nestedExplicitSubstitution body [argument] = .subst body argument :=
  rfl

theorem nestedExplicitSubstitution_pair (body first second : Pattern) :
    nestedExplicitSubstitution body [first, second] =
      .subst (.subst body first) second :=
  rfl

private def unaryNestedRule : RuleSchema where
  id := ⟨"$oslf:family:unary-nested"⟩
  metavariables := [("body", 1), ("argument", 0)]
  premises := []
  conclusion :=
    .apply "$oslf:family:judgment"
      [nestedExplicitSubstitution (.fvar "body") [.fvar "argument"]]

/-- Unary explicit substitution respects the exact occurrence-depth wire. -/
theorem unary_nested_rule_locally_valid :
    schemaLocallyValid unaryNestedRule = true := by
  simp [schemaLocallyValid, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, unaryNestedRule, nestedExplicitSubstitution,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

private def binaryNestedRule : RuleSchema where
  id := ⟨"$oslf:family:binary-nested"⟩
  metavariables :=
    [("body", 2), ("first", 0), ("second", 0)]
  premises := []
  conclusion :=
    .apply "$oslf:family:judgment"
      [ nestedExplicitSubstitution (.fvar "body")
          [.fvar "first", .fvar "second"]
      , .fvar "first" ]

/-- In the naive binary encoding the first argument occurs once below the
outer substitution binder and once at top level. -/
theorem binary_nested_occurrences :
    schemaOccurrences binaryNestedRule =
      [("body", 2), ("first", 1), ("second", 0), ("first", 0)] := by
  simp [schemaOccurrences, RuleSchema.occurrences, RuleSchema.patterns,
    binaryNestedRule, nestedExplicitSubstitution,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt]

/-- One exact-depth declaration cannot authorize both occurrences. -/
theorem binary_nested_first_has_incompatible_depths :
    ("first", 1) ∈ schemaOccurrences binaryNestedRule ∧
      ("first", 0) ∈ schemaOccurrences binaryNestedRule := by
  simp [binary_nested_occurrences]

/-- Consequently the naive binary schema is correctly rejected. -/
theorem binary_nested_rule_rejected :
    schemaLocallyValid binaryNestedRule = false := by
  simp [schemaLocallyValid, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, binaryNestedRule, nestedExplicitSubstitution,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt]

/-! ## First-order family application -/

/-- Defunctionalized application of one contextual result family.  The label
is occurrence-specific in generated calculi; the family and arguments remain
ordinary ordered constructor fields. -/
def applyFamily (label : String) (family : Pattern)
    (arguments : List Pattern) : Pattern :=
  .apply label (family :: arguments)

/-- Fail-closed observation of an occurrence-specific family application. -/
def applyFamilyArgs? (label : String) : Pattern → Option (Pattern × List Pattern)
  | .apply actual (family :: arguments) =>
      if actual = label then some (family, arguments) else none
  | _ => none

@[simp] theorem applyFamilyArgs?_applyFamily (label : String)
    (family : Pattern) (arguments : List Pattern) :
    applyFamilyArgs? label (applyFamily label family arguments) =
      some (family, arguments) := by
  simp [applyFamilyArgs?, applyFamily]

theorem applyFamily_injective (label : String)
    {firstFamily secondFamily : Pattern}
    {firstArguments secondArguments : List Pattern}
    (equality :
      applyFamily label firstFamily firstArguments =
        applyFamily label secondFamily secondArguments) :
    firstFamily = secondFamily ∧ firstArguments = secondArguments := by
  have observed := congrArg (applyFamilyArgs? label) equality
  simpa using observed

private def binaryFirstOrderRule : RuleSchema where
  id := ⟨"$oslf:family:binary-first-order"⟩
  metavariables :=
    [("family", 0), ("first", 0), ("second", 0)]
  premises := []
  conclusion :=
    .apply "$oslf:family:judgment"
      [ applyFamily "$oslf:family:apply-2" (.fvar "family")
          [.fvar "first", .fvar "second"]
      , .fvar "first" ]

/-- Defunctionalization leaves every reusable schema value at depth zero. -/
theorem binary_first_order_occurrences :
    schemaOccurrences binaryFirstOrderRule =
      [("family", 0), ("first", 0), ("second", 0), ("first", 0)] := by
  simp [schemaOccurrences, RuleSchema.occurrences, RuleSchema.patterns,
    binaryFirstOrderRule, applyFamily, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt]

/-- The corresponding first-order schema passes the same exact checker. -/
theorem binary_first_order_rule_locally_valid :
    schemaLocallyValid binaryFirstOrderRule = true := by
  simp [schemaLocallyValid, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, binaryFirstOrderRule, applyFamily,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

/-! ## Positive and negative semantic controls -/

private def firstData : Pattern := .apply "$oslf:family:first" []
private def secondData : Pattern := .apply "$oslf:family:second" []
private def pairBody : Pattern :=
  .apply "$oslf:family:pair" [.bvar 1, .bvar 0]

/-- Curried instantiation respects source argument order. -/
theorem instantiateCurried_pair :
    instantiateCurried [firstData, secondData] pairBody =
      .apply "$oslf:family:pair" [firstData, secondData] := by
  simp [instantiateCurried, instantiateBVar, instantiateBVarAt,
    firstData, secondData, pairBody, liftBVars]

/-- The concrete binary family denotes the correctly ordered result. -/
theorem binary_family_denotes_ordered_pair :
    Denotes (curryLambdas 2 pairBody) [firstData, secondData]
      (.apply "$oslf:family:pair" [firstData, secondData]) := by
  exact ⟨pairBody, rfl, instantiateCurried_pair.symm⟩

/-- Swapping the result is observably different; argument order is retained. -/
theorem binary_family_does_not_denote_swapped_pair :
    ¬ Denotes (curryLambdas 2 pairBody) [firstData, secondData]
      (.apply "$oslf:family:pair" [secondData, firstData]) := by
  intro denotation
  rcases denotation with ⟨body, familyEquality, resultEquality⟩
  simp [curryLambdas] at familyEquality
  subst body
  simp [instantiateCurried, instantiateBVar, instantiateBVarAt,
    firstData, secondData, pairBody, liftBVars] at resultEquality

#print axioms unary_nested_rule_locally_valid
#print axioms binary_nested_occurrences
#print axioms binary_nested_first_has_incompatible_depths
#print axioms binary_nested_rule_rejected
#print axioms applyFamilyArgs?_applyFamily
#print axioms applyFamily_injective
#print axioms binary_first_order_occurrences
#print axioms binary_first_order_rule_locally_valid
#print axioms instantiateCurried_pair
#print axioms binary_family_denotes_ordered_pair
#print axioms binary_family_does_not_denote_swapped_pair

end Mettapedia.OSLF.Framework.ContextualFamilyApplication
