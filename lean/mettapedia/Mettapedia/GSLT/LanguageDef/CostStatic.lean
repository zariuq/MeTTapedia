import Mettapedia.GSLT.LanguageDef.ContinuationRetyping
import Mettapedia.GSLT.LanguageDef.ReflectiveStructuralCategory
import Mettapedia.GSLT.LanguageDef.SchemaTyping
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Static-theory transport for Cost

Cost retypes selected interaction continuations, so transporting equations is
not ordinary uniform symbol renaming.  The two uniform images below are the
only canonical candidates for the unchanged base theory and its hereditary
wrapped copy.  A continued theory is statically Cost-stable exactly when
those declaration-derived candidates are well sorted in the generated
continuation signature.

This makes a missing hypothesis in the informal construction explicit: an
equation mentioning an interaction principal need not survive continuation
retyping.  Such a theory is rejected by `EquationRetypable`; no malformed
equation is silently admitted by the weaker syntactic validation gate.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Reflection
open StructuralMorphism
open WellSorted
open ReflectionExtension

/-- The two declaration-derived copies of an authored static theory. -/
inductive CostStaticColor where
  | base
  | wrapped
deriving DecidableEq, Repr

namespace CostStaticColor

/-- The other declaration-derived static copy. -/
def flip : CostStaticColor → CostStaticColor
  | .base => .wrapped
  | .wrapped => .base

@[simp]
theorem flip_base : flip .base = .wrapped := rfl

@[simp]
theorem flip_wrapped : flip .wrapped = .base := rfl

@[simp]
theorem flip_flip (color : CostStaticColor) : color.flip.flip = color := by
  cases color <;> rfl

/-- A color cannot equal its opposite. -/
theorem ne_flip (color : CostStaticColor) : color ≠ color.flip := by
  cases color <;> simp

/-- With exactly two static colors, inequality determines the opposite. -/
theorem eq_flip_of_ne {left right : CostStaticColor} (different : left ≠ right) :
    right = left.flip := by
  cases left <;> cases right <;> simp_all

/-- Reserved constructor namespace for one static copy. -/
def constructorTag : CostStaticColor → String
  | .base => costBaseConstructorTag
  | .wrapped => costWrappedConstructorTag

end CostStaticColor

def costBaseEquationTag : String := "$cost:base-equation:"

def costWrappedEquationTag : String := "$cost:wrapped-equation:"

def costBaseEquationName (name : String) : String :=
  costBaseEquationTag ++ name

def costWrappedEquationName (name : String) : String :=
  costWrappedEquationTag ++ name

def costBaseReflectiveTag : String := "$cost:base-reflective:"

def costWrappedReflectiveTag : String := "$cost:wrapped-reflective:"

def costBaseReflectiveRuleTag : String := "$cost:base-reflective-rule:"

def costWrappedReflectiveRuleTag : String := "$cost:wrapped-reflective-rule:"

def costBaseReflectiveName (name : String) : String :=
  costBaseReflectiveTag ++ name

def costWrappedReflectiveName (name : String) : String :=
  costWrappedReflectiveTag ++ name

def costBaseReflectiveRuleName (name : String) : String :=
  costBaseReflectiveRuleTag ++ name

def costWrappedReflectiveRuleName (name : String) : String :=
  costWrappedReflectiveRuleTag ++ name

theorem costBaseEquationName_injective :
    Function.Injective costBaseEquationName := by
  intro left right equality
  exact (String.append_right_inj costBaseEquationTag).mp equality

theorem costWrappedEquationName_injective :
    Function.Injective costWrappedEquationName := by
  intro left right equality
  exact (String.append_right_inj costWrappedEquationTag).mp equality

theorem costBaseReflectiveName_injective :
    Function.Injective costBaseReflectiveName := by
  intro left right equality
  exact (String.append_right_inj costBaseReflectiveTag).mp equality

theorem costWrappedReflectiveName_injective :
    Function.Injective costWrappedReflectiveName := by
  intro left right equality
  exact (String.append_right_inj costWrappedReflectiveTag).mp equality

theorem costBaseReflectiveRuleName_injective :
    Function.Injective costBaseReflectiveRuleName := by
  intro left right equality
  exact (String.append_right_inj costBaseReflectiveRuleTag).mp equality

@[simp]
theorem costBaseEquationName_ne_wrapped (base wrapped : String) :
    costBaseEquationName base ≠ costWrappedEquationName wrapped := by
  intro equality
  unfold costBaseEquationName costWrappedEquationName costBaseEquationTag
    costWrappedEquationTag at equality
  change ("$cost:" ++ "base-equation:") ++ base =
    ("$cost:" ++ "wrapped-equation:") ++ wrapped at equality
  rw [String.append_assoc, String.append_assoc] at equality
  have stripped : "base-equation:" ++ base =
      "wrapped-equation:" ++ wrapped :=
    (String.append_right_inj "$cost:").mp equality
  have characters := congrArg String.toList stripped
  simp at characters

@[simp]
theorem costWrappedEquationName_ne_base (wrapped base : String) :
    costWrappedEquationName wrapped ≠ costBaseEquationName base :=
  (costBaseEquationName_ne_wrapped base wrapped).symm

@[simp]
theorem costBaseReflectiveName_ne_wrapped (base wrapped : String) :
    costBaseReflectiveName base ≠ costWrappedReflectiveName wrapped := by
  intro equality
  unfold costBaseReflectiveName costWrappedReflectiveName
    costBaseReflectiveTag costWrappedReflectiveTag at equality
  change ("$cost:" ++ "base-reflective:") ++ base =
    ("$cost:" ++ "wrapped-reflective:") ++ wrapped at equality
  rw [String.append_assoc, String.append_assoc] at equality
  have stripped : "base-reflective:" ++ base =
      "wrapped-reflective:" ++ wrapped :=
    (String.append_right_inj "$cost:").mp equality
  have characters := congrArg String.toList stripped
  simp at characters

@[simp]
theorem costWrappedReflectiveName_ne_base (wrapped base : String) :
    costWrappedReflectiveName wrapped ≠ costBaseReflectiveName base :=
  (costBaseReflectiveName_ne_wrapped base wrapped).symm

/-- Uniform symbol action for the unchanged base copy of the static theory. -/
def costBaseStaticSymbols : LanguageDefSymbolMap :=
  { costBaseLanguageDefSymbolMap with
    equation := costBaseEquationName }

/-- Reflection-namespace action paired with the base static symbol action. -/
def costBaseStaticReflectiveSymbols : ReflectiveSymbols where
  toLanguageDefSymbolMap := costBaseStaticSymbols
  reflection :=
    { presentation := costBaseReflectiveName
      rule := costBaseReflectiveRuleName }

/-- Uniform symbol action for the hereditary wrapped copy of the static
theory.  Its sort action agrees exactly with `costWrappedTypeExpr`. -/
def costWrappedStaticSymbols (theory : IGSLT) : LanguageDefSymbolMap where
  sort := fun sort =>
    if sort = theory.presentation.interactingSort.1.name then
      costWrappedSortName
    else
      costBaseSortName sort
  constructor := costWrappedConstructorName
  relation := id
  equation := costWrappedEquationName
  rewrite := id

/-- Reflection-namespace action paired with the wrapped static symbol action. -/
def costWrappedStaticReflectiveSymbols (theory : IGSLT) :
    ReflectiveSymbols where
  toLanguageDefSymbolMap := costWrappedStaticSymbols theory
  reflection :=
    { presentation := costWrappedReflectiveName
      rule := costWrappedReflectiveRuleName }

@[simp]
theorem mapTypeExpr_costBaseStaticSymbols (type : TypeExpr) :
    mapTypeExpr costBaseStaticSymbols type = costBaseTypeExpr type := by
  induction type <;>
    simp_all [costBaseStaticSymbols, costBaseLanguageDefSymbolMap,
      mapTypeExpr, costBaseTypeExpr]

@[simp]
theorem mapTypeExpr_costWrappedStaticSymbols (theory : IGSLT)
    (type : TypeExpr) :
    mapTypeExpr (costWrappedStaticSymbols theory) type =
      costWrappedTypeExpr theory.presentation.interactingSort.1.name type := by
  induction type with
  | base sort =>
      by_cases equality :
          sort = theory.presentation.interactingSort.1.name <;>
        simp [costWrappedStaticSymbols, mapTypeExpr, costWrappedTypeExpr,
          equality]
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      simp only [mapTypeExpr, costWrappedTypeExpr]
      rw [domainHypothesis, codomainHypothesis]
  | multiBinder body inductionHypothesis =>
      simp only [mapTypeExpr, costWrappedTypeExpr]
      rw [inductionHypothesis]
  | collection collectionType body inductionHypothesis =>
      simp only [mapTypeExpr, costWrappedTypeExpr]
      rw [inductionHypothesis]

@[simp]
theorem mapPattern_costBaseStaticSymbols (pattern : Pattern) :
    mapPattern costBaseStaticSymbols pattern =
      mapPattern costBaseLanguageDefSymbolMap pattern := by
  induction pattern using Pattern.inductionOn <;>
    simp_all [costBaseStaticSymbols, costBaseLanguageDefSymbolMap,
      mapPattern, List.map_inj_left]

/-- The declaration-derived base equation candidate. -/
def costBaseEquation (equation : Equation) : Equation :=
  mapEquation costBaseStaticSymbols equation

/-- The declaration-derived hereditary wrapped equation candidate. -/
def costWrappedEquation (theory : IGSLT) (equation : Equation) : Equation :=
  mapEquation (costWrappedStaticSymbols theory) equation

/-- Base-fiber image of one authored reflective static presentation. -/
def costBaseReflectivePresentationDecl
    (declaration : ReflectivePresentationDecl) :
    ReflectivePresentationDecl :=
  mapReflectivePresentation costBaseStaticReflectiveSymbols declaration

/-- Hereditary wrapped-fiber image of one authored reflective static
presentation. -/
def costWrappedReflectivePresentationDecl (theory : IGSLT)
    (declaration : ReflectivePresentationDecl) :
    ReflectivePresentationDecl :=
  mapReflectivePresentation (costWrappedStaticReflectiveSymbols theory)
    declaration

/-- Exact intermediate language used to validate reflective static transport.
It adds no Cost apparatus or reduction: only the two declaration-derived
images of the source equations and reflective presentations. -/
def reflectiveRetypingLanguage {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) : LanguageDef :=
  { plan.generatedLanguage with
    equations :=
      theory.presentation.presentation.language.equations.map
          costBaseEquation ++
        theory.presentation.presentation.language.equations.map
          (costWrappedEquation theory) }

mutual
  /-- A schema contains no open collection-tail metavariable.  Such tails
  have a shape-sensitive fallback in gradual binding application, so an
  arbitrary injective renaming does not commute with that fallback. -/
  def schemaHasNoCollectionRest : Pattern → Bool
    | .bvar _ | .fvar _ => true
    | .apply _ arguments => schemaListHasNoCollectionRest arguments
    | .lambda _ body => schemaHasNoCollectionRest body
    | .multiLambda _ _ body => schemaHasNoCollectionRest body
    | .subst body replacement =>
        schemaHasNoCollectionRest body && schemaHasNoCollectionRest replacement
    | .collection _ elements rest =>
        rest.isNone && schemaListHasNoCollectionRest elements

  /-- List companion to `schemaHasNoCollectionRest`. -/
  def schemaListHasNoCollectionRest : List Pattern → Bool
    | [] => true
    | pattern :: patterns =>
        schemaHasNoCollectionRest pattern &&
          schemaListHasNoCollectionRest patterns
end

/-- Exact syntactic fragment on which schema-name transport commutes with
gradual instantiation on every covered binding environment.  Canonical
locally nameless metadata makes binder display names inert, while closed
collection tails remove the only shape-sensitive unresolved-name fallback. -/
def schemaInstantiationStable (pattern : Pattern) : Bool :=
  pattern.hasCanonicalBinderMetadata && schemaHasNoCollectionRest pattern

/-- Pointwise stability of an argument or collection-element list. -/
def schemaListInstantiationStable (patterns : List Pattern) : Bool :=
  Pattern.hasCanonicalBinderMetadataList patterns &&
    schemaListHasNoCollectionRest patterns

mutual
  /-- Renaming presentation symbols changes neither collection-tail
  closure nor any other schema-instantiation boundary. -/
  @[simp]
  theorem schemaHasNoCollectionRest_mapPattern
      (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
      schemaHasNoCollectionRest (mapPattern symbols pattern) =
        schemaHasNoCollectionRest pattern := by
    cases pattern with
    | bvar index => rfl
    | fvar name => rfl
    | apply constructor arguments =>
        simp [mapPattern, mapPatternList_eq_map,
          schemaHasNoCollectionRest,
          schemaListHasNoCollectionRest_map]
    | lambda binder body =>
        simp [mapPattern, schemaHasNoCollectionRest,
          schemaHasNoCollectionRest_mapPattern]
    | multiLambda arity binders body =>
        simp [mapPattern, schemaHasNoCollectionRest,
          schemaHasNoCollectionRest_mapPattern]
    | subst body replacement =>
        simp [mapPattern, schemaHasNoCollectionRest,
          schemaHasNoCollectionRest_mapPattern]
    | collection collectionType elements rest =>
        simp [mapPattern, mapPatternList_eq_map,
          schemaHasNoCollectionRest,
          schemaListHasNoCollectionRest_map]

  /-- List companion to `schemaHasNoCollectionRest_mapPattern`. -/
  @[simp]
  theorem schemaListHasNoCollectionRest_map
      (symbols : LanguageDefSymbolMap) (patterns : List Pattern) :
      schemaListHasNoCollectionRest
          (patterns.map (mapPattern symbols)) =
        schemaListHasNoCollectionRest patterns := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp [schemaListHasNoCollectionRest,
          schemaHasNoCollectionRest_mapPattern,
          schemaListHasNoCollectionRest_map]
end

/-- Stable schema instantiation is invariant under structural symbol
renaming. -/
@[simp]
theorem schemaInstantiationStable_mapPattern
    (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    schemaInstantiationStable (mapPattern symbols pattern) =
      schemaInstantiationStable pattern := by
  simp [schemaInstantiationStable]

mutual
  /-- The matcher-correct fragment depends only on pattern shape, not on
  presentation labels. -/
  @[simp]
  theorem isMatchCorrectAux_mapPattern
      (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
      isMatchCorrectAux (mapPattern symbols pattern) =
        isMatchCorrectAux pattern := by
    cases pattern with
    | bvar index => rfl
    | fvar name => rfl
    | apply constructor arguments =>
        simp [mapPattern, mapPatternList_eq_map, isMatchCorrectAux,
          isMatchCorrectListAux_map]
    | lambda binder body => rfl
    | multiLambda arity binders body => rfl
    | subst body replacement => rfl
    | collection collectionType elements rest => rfl

  /-- List companion to `isMatchCorrectAux_mapPattern`. -/
  @[simp]
  theorem isMatchCorrectListAux_map
      (symbols : LanguageDefSymbolMap) (patterns : List Pattern) :
      isMatchCorrectListAux (patterns.map (mapPattern symbols)) =
        isMatchCorrectListAux patterns := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp [isMatchCorrectListAux, isMatchCorrectAux_mapPattern,
          isMatchCorrectListAux_map]
end

/-- Public matcher-correctness invariance under structural symbol renaming. -/
@[simp]
theorem isMatchCorrect_mapPattern
    (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    Pattern.isMatchCorrect (mapPattern symbols pattern) =
      Pattern.isMatchCorrect pattern := by
  exact isMatchCorrectAux_mapPattern symbols pattern

/-- Stable schema transport does not by itself imply exact matcher
reconstruction.  In particular, binder schemas have canonical metadata and
no collection tail, but the current matcher deliberately excludes them from
its reconstruction theorem because bindings do not record their source
depth. -/
theorem schemaInstantiationStable_does_not_imply_matchCorrect :
    schemaInstantiationStable (.lambda none (.fvar "x")) = true ∧
      Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect
        (.lambda none (.fvar "x")) = false := by
  exact ⟨rfl, rfl⟩

/-- Every member of a stable schema list is itself stable. -/
theorem schemaInstantiationStable_of_mem
    {patterns : List Pattern} (stable : schemaListInstantiationStable patterns = true)
    {pattern : Pattern} (membership : pattern ∈ patterns) :
    schemaInstantiationStable pattern = true := by
  induction patterns with
  | nil => cases membership
  | cons head tail inductionHypothesis =>
      simp only [schemaListInstantiationStable,
        Pattern.hasCanonicalBinderMetadataList,
        schemaListHasNoCollectionRest, Bool.and_eq_true] at stable
      rcases List.mem_cons.mp membership with rfl | tailMembership
      · simp only [schemaInstantiationStable, Bool.and_eq_true]
        exact ⟨stable.1.1, stable.2.1⟩
      · apply inductionHypothesis
        · simp only [schemaListInstantiationStable, Bool.and_eq_true]
          exact ⟨stable.1.2, stable.2.2⟩
        · exact tailMembership

/-- One authored equation has the exact static data needed by the Cost lift.

The two sorting fields retain the original declaration-derived retyping
obligation.  The premise, instantiation, and matcher fields state the
additional operational boundary explicitly: this first exact transport
handles no premise evaluator, both orientations must commute with the
injective schema namespace used by generated Cost equations, and both sides
must reconstruct their matched instances exactly. -/
structure EquationRetypable {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (equation : Equation) : Prop where
  premiseFree : equation.premises = []
  leftInstantiationStable : schemaInstantiationStable equation.left = true
  rightInstantiationStable : schemaInstantiationStable equation.right = true
  leftMatchCorrect :
    Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect equation.left = true
  rightMatchCorrect :
    Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect equation.right = true
  baseWellSorted :
    EquationWellSorted plan.generatedLanguage (costBaseEquation equation)
  wrappedWellSorted :
    EquationWellSorted plan.generatedLanguage
      (costWrappedEquation theory equation)

/-- Every equation of the sole authored source presentation survives the
same deterministic Cost transport. -/
def EquationsRetypable {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) : Prop :=
  ∀ equation ∈ theory.presentation.presentation.language.equations,
    EquationRetypable plan equation

/-- One reflective presentation survives Cost when both deterministic images
pass the existing reflective validator in the exact generated continuation
signature.  This checks sorts, constructor profiles, uniqueness, and the
quote/drop equation; no parallel notion of reflective validity is introduced. -/
def ReflectivePresentationRetypable {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    (declaration : ReflectivePresentationDecl) : Prop :=
  ((reflectiveRetypingLanguage plan).validateReflectivePresentation
      (costBaseReflectivePresentationDecl declaration) = []) ∧
    ((reflectiveRetypingLanguage plan).validateReflectivePresentation
      (costWrappedReflectivePresentationDecl theory declaration) = [])

/-- Every authored reflective presentation is stable under the same exact
hereditary continuation retyping. -/
def ReflectivePresentationsRetypable {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    (profile : ReflectionProfile) : Prop :=
  ∀ declaration ∈ profile.presentations,
    ReflectivePresentationRetypable plan declaration

/-- Base-copy equation transport commutes with erasing the reserved symbol
tags back to the source declaration. -/
theorem costBaseEquation_left (equation : Equation) :
    (costBaseEquation equation).left =
      mapPattern costBaseLanguageDefSymbolMap equation.left := by
  simp [costBaseEquation, mapEquation]

/-- The wrapped candidate uses the wrapped constructor namespace
uniformly.  Equations containing a principal constructor therefore fail the
sorting obligation instead of receiving an arbitrary mixed interpretation. -/
theorem costWrappedEquation_left (theory : IGSLT) (equation : Equation) :
    (costWrappedEquation theory equation).left =
      mapPattern (costWrappedStaticSymbols theory) equation.left := by
  rfl

end Mettapedia.GSLT.LanguageDef
