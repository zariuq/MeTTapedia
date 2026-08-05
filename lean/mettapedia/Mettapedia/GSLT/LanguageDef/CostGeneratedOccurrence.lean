import Mettapedia.GSLT.LanguageDef.CostCanonicalSection
import Mettapedia.GSLT.LanguageDef.EquationOccurrence

/-!
# Authored origins of generated Cost occurrences

Every ordinary or reflective generator in a Cost language is one of the two
static images of an authored source declaration.  This module retains that
origin in `Type` and proves coverage for the proof-relevant occurrence layer.
Equation and reflection remain distinct until a later semantic normalization
span evaluates them.
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
    source.theory.presentation.presentation.language.reflectivePresentations
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
      source.costWholeLanguage.reflectivePresentations) :
    Nonempty (CostReflectiveDeclarationOrigin source target) := by
  have staticMembership : target ∈
      source.costStaticReflectivePresentations := by
    simpa only [CIGSLT.costWholeLanguage_reflectivePresentations] using
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
    (witness : EquationSemantics.AuthoredEquationInstanceWitness
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
    (witness : EquationSemantics.AuthoredEquationInstanceWitness
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
    (witness : EquationSemantics.AuthoredGeneratorWitness
      defaultBasePremises source.costWholeLanguage left right) : Type :=
  match witness with
  | .equation _ instanceWitness =>
      CostEquationInstanceOrigin source instanceWitness
  | .reflective _ declaration _ =>
      CostReflectiveDeclarationOrigin source declaration.1

/-- The generated Cost declaration lists exhaust the proof-relevant
generator layer: every occurrence comes from one authored source declaration
in one exact static colour. -/
theorem nonempty_costAuthoredGeneratorOrigin
    (source : CIGSLT) {left right : Pattern}
    (witness : EquationSemantics.AuthoredGeneratorWitness
      defaultBasePremises source.costWholeLanguage left right) :
    Nonempty (CostAuthoredGeneratorOrigin source witness) := by
  cases witness with
  | equation context instanceWitness =>
      exact nonempty_costEquationInstanceOrigin source instanceWitness
  | reflective context declaration representatives =>
      exact nonempty_costReflectiveDeclarationOrigin_of_mem source
        declaration.2

/-- Static colour retained by an authored generated-occurrence origin. -/
def CostAuthoredGeneratorOrigin.color
    {source : CIGSLT} {left right : Pattern}
    {witness : EquationSemantics.AuthoredGeneratorWitness
      defaultBasePremises source.costWholeLanguage left right} :
    CostAuthoredGeneratorOrigin source witness → CostStaticColor :=
  match witness with
  | .equation _ instanceWitness =>
      match instanceWitness with
      | .forward _ _ _ _ _ _ _ => fun origin =>
          CostEquationDeclarationOrigin.color origin
      | .reverse _ _ _ _ _ _ _ => fun origin =>
          CostEquationDeclarationOrigin.color origin
  | .reflective _ _ _ => fun origin =>
      CostReflectiveDeclarationOrigin.color origin

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
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree
      targetBound targetSort}
    (generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right) where
  witness : EquationSemantics.AuthoredGeneratorWitness defaultBasePremises
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
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree
      targetBound targetSort}
    (generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right) :
    Nonempty (CostTypedGeneratorOccurrence source generator) := by
  obtain ⟨witness, erasesTo⟩ :=
    EquationSemantics.AuthoredGeneratorWitness.exists_erasing_to generator
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
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree
      targetBound targetSort}
    {generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right}
    (occurrence : CostTypedGeneratorOccurrence source generator) :
    CostStaticColor := occurrence.origin.color

end CostTypedGeneratorOccurrence

end Mettapedia.GSLT.LanguageDef
