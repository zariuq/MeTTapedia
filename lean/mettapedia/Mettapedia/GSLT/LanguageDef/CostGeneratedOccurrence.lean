import Mettapedia.GSLT.LanguageDef.CostCanonicalSection
import Mettapedia.GSLT.LanguageDef.ReflectiveEquationOccurrence

/-!
# Authored origins of generated Cost occurrences

Every ordinary or reflective generator in a Cost language is one of the two
static images of an authored source declaration, and every presentation-derived
generator is a law of an authored collection carrier or algebra rule of the
generated language.  This module retains that origin in `Type` and proves
coverage for the proof-relevant occurrence layer.  Equation, reflection, and
derived law remain distinct until a later semantic normalization span
evaluates them; a derived law has no static colour of its own.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

namespace EquationSemantics.DerivedGeneratorWitness

/-- The declaring collection-carrier or algebra rule of a presentation-derived
occurrence. -/
def rule {language : LanguageDef} {left right : Pattern} :
    DerivedGeneratorWitness language left right → GrammarRule
  | .bagPerm rule _ _ _ _ _ => rule
  | .setPerm rule _ _ _ _ _ => rule
  | .setDedup rule _ _ _ _ => rule
  | .flatten rule _ _ _ _ _ _ _ _ => rule
  | .singleton rule _ _ _ _ _ _ => rule
  | .unitElim rule _ _ _ _ _ _ _ _ => rule
  | .emptyUnit rule _ _ _ _ _ _ => rule

/-- The declaring rule is authored by the language. -/
theorem rule_mem {language : LanguageDef} {left right : Pattern} :
    (witness : DerivedGeneratorWitness language left right) →
      witness.rule ∈ language.terms
  | .bagPerm _ _ _ carrier _ _ => carrier.authored
  | .setPerm _ _ _ carrier _ _ => carrier.authored
  | .setDedup _ _ _ carrier _ => carrier.authored
  | .flatten _ _ _ _ _ _ algebra _ _ => algebra.authored
  | .singleton _ _ _ _ algebra _ _ => algebra.authored
  | .unitElim _ _ _ _ _ _ algebra _ _ => algebra.authored
  | .emptyUnit _ _ _ _ algebra _ _ => algebra.authored

end EquationSemantics.DerivedGeneratorWitness

/-- Origin of a presentation-derived occurrence: the declaring carrier or
algebra rule, authored by the generated Cost language.  Such a law is not the
static image of a coloured declaration. -/
structure CostDerivedGeneratorOrigin (source : CIGSLT) (rule : GrammarRule) : Type where
  membership : rule ∈ source.costWholeLanguage.terms

/-- Exact authored source and colour of one generated Cost equation
declaration. -/
structure CostEquationDeclarationOrigin (source : CIGSLT)
    (target : Equation) where
  color : CostStaticColor
  sourceEquation : Equation
  sourceMembership : sourceEquation ∈
    source.theory.presentation.presentation.language.equations
  target_eq : target =
    costStaticEquationDecl source color sourceEquation

/-- Exact authored source and colour of one generated reflective
declaration. -/
structure CostReflectiveDeclarationOrigin (source : CIGSLT)
    (target : ReflectivePresentationDecl) where
  color : CostStaticColor
  sourceDeclaration : ReflectivePresentationDecl
  sourceMembership : sourceDeclaration ∈
    source.reflection.1.presentations
  target_eq : target = costStaticReflectivePresentationDecl source color
    sourceDeclaration

/-- Membership in the generated equation table has a retained two-colour
authored origin. -/
theorem nonempty_costEquationDeclarationOrigin_of_mem
    (source : CIGSLT) {target : Equation}
    (membership : target ∈ source.costWholeLanguage.equations) :
    Nonempty (CostEquationDeclarationOrigin source target) := by
  have staticMembership : target ∈ source.costStaticEquations := by
    simpa only [CIGSLT.costWholeLanguage_equations] using membership
  obtain ⟨color, sourceEquation, sourceMembership, target_eq⟩ :=
    (mem_costStaticEquations_iff_exists_source source).1 staticMembership
  exact ⟨⟨color, sourceEquation, sourceMembership, target_eq⟩⟩

/-- Membership in the generated reflective table has a retained two-colour
authored origin. -/
theorem nonempty_costReflectiveDeclarationOrigin_of_mem
    (source : CIGSLT) {target : ReflectivePresentationDecl}
    (membership : target ∈
      source.costWholeReflectionProfile.presentations) :
    Nonempty (CostReflectiveDeclarationOrigin source target) := by
  have staticMembership : target ∈
      source.costStaticReflectivePresentations := by
    simpa only [CIGSLT.costWholeReflectionProfile_presentations] using
      membership
  obtain ⟨color, sourceDeclaration, sourceMembership, target_eq⟩ :=
    (mem_costStaticReflectivePresentations_iff_exists_source source).1
      staticMembership
  exact ⟨⟨color, sourceDeclaration, sourceMembership, target_eq⟩⟩

/-- Declaration origin selected by a proof-relevant equation instance.  The
instance itself continues to retain orientation, bindings, premise evidence,
and exact endpoints. -/
def CostEquationInstanceOrigin (source : CIGSLT)
    {redex contractum : Pattern}
    (witness : EquationSemantics.DeclaredEquationInstanceWitness
      defaultBasePremises source.costWholeLanguage redex contractum) : Type :=
  match witness with
  | .forward _ equation _ _ _ _ _ =>
      CostEquationDeclarationOrigin source equation.1
  | .reverse _ equation _ _ _ _ _ =>
      CostEquationDeclarationOrigin source equation.1

/-- Every proof-relevant generated Cost equation instance retains an authored
declaration origin. -/
theorem nonempty_costEquationInstanceOrigin
    (source : CIGSLT) {redex contractum : Pattern}
    (witness : EquationSemantics.DeclaredEquationInstanceWitness
      defaultBasePremises source.costWholeLanguage redex contractum) :
    Nonempty (CostEquationInstanceOrigin source witness) := by
  cases witness with
  | forward fuel equation initialBindings finalBindings matched premises
      target_eq =>
      exact nonempty_costEquationDeclarationOrigin_of_mem source equation.2
  | reverse fuel equation initialBindings finalBindings matched premises
      target_eq =>
      exact nonempty_costEquationDeclarationOrigin_of_mem source equation.2

/-- Authored two-colour provenance selected by either form of a
proof-relevant generated Cost generator.  The match deliberately preserves
the equation/reflection distinction. -/
def CostAuthoredGeneratorOrigin (source : CIGSLT)
    {left right : Pattern}
    (witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage left right) : Type :=
  match witness with
  | .core (.equation _ instanceWitness) =>
      CostEquationInstanceOrigin source instanceWitness
  | .core (.derived _ lawWitness) =>
      CostDerivedGeneratorOrigin source lawWitness.rule
  | .reflective _ declaration _ =>
      CostReflectiveDeclarationOrigin source declaration.1

/-- The generated Cost declaration lists exhaust the proof-relevant
generator layer: every occurrence comes from one authored source declaration
in one exact static colour. -/
theorem nonempty_costAuthoredGeneratorOrigin
    (source : CIGSLT) {left right : Pattern}
    (witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage left right) :
    Nonempty (CostAuthoredGeneratorOrigin source witness) := by
  cases witness with
  | core witness =>
      cases witness with
      | equation context instanceWitness =>
          exact nonempty_costEquationInstanceOrigin source instanceWitness
      | derived context lawWitness =>
          exact ⟨⟨lawWitness.rule_mem⟩⟩
  | reflective context declaration representatives =>
      exact nonempty_costReflectiveDeclarationOrigin_of_mem source
        declaration.2

/-- Static colour retained by an authored generated-occurrence origin: the
colour of the selected declaration, and none for a presentation-derived
occurrence, which is not the image of a coloured declaration. -/
def CostAuthoredGeneratorOrigin.color
    {source : CIGSLT} {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage left right} :
    CostAuthoredGeneratorOrigin source witness → Option CostStaticColor :=
  match witness with
  | .core (.equation _ instanceWitness) =>
      match instanceWitness with
      | .forward _ _ _ _ _ _ _ => fun origin =>
          some (CostEquationDeclarationOrigin.color origin)
      | .reverse _ _ _ _ _ _ _ => fun origin =>
          some (CostEquationDeclarationOrigin.color origin)
  | .core (.derived _ _) => fun _ => none
  | .reflective _ _ _ => fun origin =>
      some (CostReflectiveDeclarationOrigin.color origin)

/-- A typed generated Cost edge together with its exact proof-relevant
occurrence and authored two-colour declaration origin.

Endpoint typing is carried by the indexed `OpenTerm`s.  Equation versus
reflection, equation orientation, bindings, redex context, source
declaration, and static colour all remain available before support erasure. -/
structure CostTypedGeneratorOccurrence
    (source : CIGSLT)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      targetBound targetSort}
    (generator : ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage targetFree targetBound (.base targetSort.1)
      left right) where
  witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
    source.costWholeReflectionProfile defaultBasePremises
    source.costWholeLanguage left.1 right.1
  erasesTo : witness.erase = generator
  origin : CostAuthoredGeneratorOrigin source witness

/-- Every typed generated Cost edge has a non-lossy occurrence above its
proposition-valued support relation.  This is coverage, not a choice of
normalization alignment. -/
theorem nonempty_costTypedGeneratorOccurrence
    (source : CIGSLT)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      targetBound targetSort}
    (generator : ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage targetFree targetBound (.base targetSort.1)
      left right) :
    Nonempty (CostTypedGeneratorOccurrence source generator) := by
  obtain ⟨witness, erasesTo⟩ :=
    ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness.exists_erasing_to
      generator
  obtain ⟨origin⟩ := nonempty_costAuthoredGeneratorOrigin source witness
  exact ⟨⟨witness, erasesTo, origin⟩⟩

namespace CostTypedGeneratorOccurrence

/-- Static colour of the exact generated declaration selected by a typed
occurrence; none for a presentation-derived occurrence. -/
def declarationColor
    {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      targetBound targetSort}
    {generator : ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage targetFree targetBound (.base targetSort.1)
      left right}
    (occurrence : CostTypedGeneratorOccurrence source generator) :
    Option CostStaticColor := occurrence.origin.color

end CostTypedGeneratorOccurrence

end Mettapedia.GSLT.LanguageDef
