import Mettapedia.GSLT.LanguageDef.CostCanonicalSection
import Mettapedia.GSLT.LanguageDef.ReflectiveEquationOccurrence

/-!
# Authored origins of generated Cost occurrences

Every equation, collection law, or reflective generator in a Cost language
retains its authored declaration origin. This module keeps that origin in
`Type` and proves coverage for the proof-relevant occurrence layer. Collection
laws retain their declaring constructor and its static copy; equations and
reflection retain their respective declaration tables.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

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

/-- Administrative constructors cannot license a bare collection law. -/
theorem costApparatusConstructor_not_collection
    (constructor : CostApparatusConstructor) (interactingSort : String) :
    ¬ ∃ name kind elementType,
      (constructor.grammarRule interactingSort).params =
        [.simple name (.collection kind elementType)] := by
  cases constructor <;>
    simp [CostApparatusConstructor.grammarRule, costSignatureUnitConstructor,
      costSignatureProductConstructor, costSignedConstructor,
      costTokenStackEmptyConstructor, costTokenStackConsConstructor,
      costFundingConstructor, costContactConstructor]

/-- The exact generated constructor licensing a collection law. Its intrinsic
identity retains the source constructor and whether the copy is base or wrapped.
The collection shape excludes every administrative constructor. -/
structure CostCollectionDeclarationOrigin (source : CIGSLT)
    (target : GrammarRule) where
  constructor : source.DeclaredCostConstructor
  target_eq : source.materializeDeclaredCostConstructor constructor = target
  collection : ∃ name kind elementType,
    target.params = [.simple name (.collection kind elementType)]

def CostCollectionDeclarationOrigin.color
    {source : CIGSLT} {target : GrammarRule}
    (origin : CostCollectionDeclarationOrigin source target) : CostStaticColor := by
  rcases origin with ⟨⟨constructor, declared⟩, target_eq, collection⟩
  cases constructor with
  | base _ => exact .base
  | wrapped _ => exact .wrapped
  | apparatus constructor =>
      apply False.elim
      apply costApparatusConstructor_not_collection constructor
        source.theory.presentation.interactingSort.1.name
      subst target
      exact collection

/-- Recover the exact authored constructor, including its declaration membership. -/
def CostCollectionDeclarationOrigin.sourceConstructor
    {source : CIGSLT} {target : GrammarRule}
    (origin : CostCollectionDeclarationOrigin source target) :
    StructuralMorphism.DeclaredConstructor source.theory.presentation.presentation := by
  rcases origin with ⟨⟨constructor, declared⟩, target_eq, collection⟩
  cases constructor with
  | base constructor => exact constructor
  | wrapped constructor => exact constructor
  | apparatus constructor =>
      apply False.elim
      apply costApparatusConstructor_not_collection constructor
        source.theory.presentation.interactingSort.1.name
      subst target
      exact collection

theorem nonempty_costCollectionDeclarationOrigin
    (source : CIGSLT) {left right : Pattern}
    (witness : EquationSemantics.DerivedGeneratorWitness
      source.costWholeLanguage left right) :
    Nonempty (CostCollectionDeclarationOrigin source witness.declaration) := by
  obtain ⟨constructor, target_eq⟩ :=
    source.exists_declaredCostConstructor_of_mem witness.declaration
      (by simpa only [source.costWholeLanguage_terms] using witness.declaration_mem)
  exact ⟨⟨constructor, target_eq, witness.declaration_collection⟩⟩

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

/-- Authored two-colour provenance selected by a proof-relevant generated
Cost generator, preserving equations, collection laws, and reflection. -/
def CostAuthoredGeneratorOrigin (source : CIGSLT)
    {left right : Pattern}
    (witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage left right) : Type :=
  match witness with
  | .core (.equation _ instanceWitness) =>
      CostEquationInstanceOrigin source instanceWitness
  | .core (.derived _ lawWitness) =>
      CostCollectionDeclarationOrigin source lawWitness.declaration
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
          exact nonempty_costCollectionDeclarationOrigin source lawWitness
  | reflective context declaration representatives =>
      exact nonempty_costReflectiveDeclarationOrigin_of_mem source
        declaration.2

/-- Static colour retained by an authored generated-occurrence origin. -/
def CostAuthoredGeneratorOrigin.color
    {source : CIGSLT} {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage left right} :
    CostAuthoredGeneratorOrigin source witness → CostStaticColor :=
  match witness with
  | .core (.equation _ instanceWitness) =>
      match instanceWitness with
      | .forward _ _ _ _ _ _ _ => fun origin =>
          CostEquationDeclarationOrigin.color origin
      | .reverse _ _ _ _ _ _ _ => fun origin =>
          CostEquationDeclarationOrigin.color origin
  | .core (.derived _ _) => fun origin =>
      CostCollectionDeclarationOrigin.color origin
  | .reflective _ _ _ => fun origin =>
      CostReflectiveDeclarationOrigin.color origin

/-- A typed generated Cost edge together with its exact proof-relevant
occurrence and authored two-colour declaration origin.

Endpoint typing is carried by the indexed `OpenTerm`s. Equation, collection
law, or reflection provenance, equation orientation, bindings, redex context, source
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
occurrence. -/
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
    CostStaticColor := occurrence.origin.color

end CostTypedGeneratorOccurrence

#print axioms costApparatusConstructor_not_collection
#print axioms nonempty_costCollectionDeclarationOrigin
#print axioms nonempty_costAuthoredGeneratorOrigin
#print axioms nonempty_costTypedGeneratorOccurrence

end Mettapedia.GSLT.LanguageDef
