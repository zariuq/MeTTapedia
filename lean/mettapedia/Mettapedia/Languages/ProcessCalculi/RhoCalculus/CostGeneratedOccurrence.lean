import Mettapedia.GSLT.LanguageDef.CostGeneratedOccurrence
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-!
# Exact authored origins of generated rho Cost occurrences

Pure rho has one authored static equation and one authored reflective
presentation.  Consequently every proof-relevant generator in the first Cost
language retains an exact base-or-wrapped image of Quote/Drop data; there is
no third declaration family.  This is declaration classification only.
Whether an occurrence is selected by, foreign to, or crosses a particular
region decomposition remains a separate typed theorem.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open LanguageDefGSLT
open LanguageDefContinuedInteraction

/-- Exact colour of a generated copy of rho's sole QuoteDrop equation. -/
structure RhoCostEquationDeclarationOrigin (target : Equation) where
  color : CostStaticColor
  target_eq : target =
    costStaticEquationDecl rhoCIGSLT color rhoCalc.equations[0]

/-- Exact colour of a generated copy of rho's sole reflective declaration. -/
structure RhoCostReflectiveDeclarationOrigin
    (target : ReflectivePresentationDecl) where
  color : CostStaticColor
  target_eq : target = costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl

/-- Generic two-colour equation provenance specializes to rho's unique
QuoteDrop equation. -/
theorem nonempty_rhoCostEquationDeclarationOrigin_of_mem
    {target : Equation}
    (membership : target ∈ rhoCIGSLT.costWholeLanguage.equations) :
    Nonempty (RhoCostEquationDeclarationOrigin target) := by
  obtain ⟨origin⟩ :=
    nonempty_costEquationDeclarationOrigin_of_mem rhoCIGSLT membership
  have source_eq : origin.sourceEquation = rhoCalc.equations[0] := by
    have sourceMembership := origin.sourceMembership
    change origin.sourceEquation ∈ [rhoCalc.equations[0]] at sourceMembership
    simpa using sourceMembership
  refine ⟨⟨origin.color, ?_⟩⟩
  exact origin.target_eq.trans (congrArg
    (costStaticEquationDecl rhoCIGSLT origin.color) source_eq)

/-- Generic two-colour reflective provenance specializes to rho's unique
reflective process declaration. -/
theorem nonempty_rhoCostReflectiveDeclarationOrigin_of_mem
    {target : ReflectivePresentationDecl}
    (membership : target ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations) :
    Nonempty (RhoCostReflectiveDeclarationOrigin target) := by
  obtain ⟨origin⟩ :=
    nonempty_costReflectiveDeclarationOrigin_of_mem rhoCIGSLT membership
  have source_eq : origin.sourceDeclaration =
      rhoReflectivePresentation.toReflectivePresentationDecl := by
    have sourceMembership := origin.sourceMembership
    change origin.sourceDeclaration ∈
      [rhoReflectivePresentation.toReflectivePresentationDecl] at sourceMembership
    simpa using sourceMembership
  refine ⟨⟨origin.color, ?_⟩⟩
  exact origin.target_eq.trans (congrArg
    (costStaticReflectivePresentationDecl rhoCIGSLT origin.color) source_eq)

/-- Exact rho declaration selected by a proof-relevant generated equation
instance.  Orientation and bindings remain in the indexed witness. -/
def RhoCostEquationInstanceOrigin {redex contractum : Pattern}
    (witness : EquationSemantics.DeclaredEquationInstanceWitness
      defaultBasePremises rhoCIGSLT.costWholeLanguage redex contractum) :
    Type :=
  match witness with
  | .forward _ equation _ _ _ _ _ =>
      RhoCostEquationDeclarationOrigin equation.1
  | .reverse _ equation _ _ _ _ _ =>
      RhoCostEquationDeclarationOrigin equation.1

/-- Static colour retained by the exact declaration origin of a generated
rho equation instance. -/
def RhoCostEquationInstanceOrigin.color
    {redex contractum : Pattern}
    {witness : EquationSemantics.DeclaredEquationInstanceWitness
      defaultBasePremises rhoCIGSLT.costWholeLanguage redex contractum} :
    RhoCostEquationInstanceOrigin witness → CostStaticColor :=
  match witness with
  | .forward _ _ _ _ _ _ _ => fun origin =>
      RhoCostEquationDeclarationOrigin.color origin
  | .reverse _ _ _ _ _ _ _ => fun origin =>
      RhoCostEquationDeclarationOrigin.color origin

/-- Every proof-relevant generated rho equation instance selects exactly one
of the base or wrapped QuoteDrop declarations. -/
theorem nonempty_rhoCostEquationInstanceOrigin
    {redex contractum : Pattern}
    (witness : EquationSemantics.DeclaredEquationInstanceWitness
      defaultBasePremises rhoCIGSLT.costWholeLanguage redex contractum) :
    Nonempty (RhoCostEquationInstanceOrigin witness) := by
  cases witness with
  | forward fuel equation initialBindings finalBindings matched premises
      target_eq =>
      exact nonempty_rhoCostEquationDeclarationOrigin_of_mem equation.2
  | reverse fuel equation initialBindings finalBindings matched premises
      target_eq =>
      exact nonempty_rhoCostEquationDeclarationOrigin_of_mem equation.2

/-- Equation and reflection classification for one proof-relevant generated
rho Cost occurrence. -/
def RhoCostAuthoredGeneratorOrigin {left right : Pattern}
    (witness :
      ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
        rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
          rhoCIGSLT.costWholeLanguage left right) : Type :=
  match witness with
  | .core (.equation _ instanceWitness) =>
      RhoCostEquationInstanceOrigin instanceWitness
  | .reflective _ declaration _ =>
      RhoCostReflectiveDeclarationOrigin declaration.1

/-- Every proof-relevant generated rho Cost occurrence is an exact coloured
image of rho's sole equation or sole reflective declaration. -/
theorem nonempty_rhoCostAuthoredGeneratorOrigin
    {left right : Pattern}
    (witness :
      ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
        rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
          rhoCIGSLT.costWholeLanguage left right) :
    Nonempty (RhoCostAuthoredGeneratorOrigin witness) := by
  cases witness with
  | core witness =>
      cases witness with
      | equation context instanceWitness =>
          exact nonempty_rhoCostEquationInstanceOrigin instanceWitness
  | reflective context declaration representatives =>
      exact nonempty_rhoCostReflectiveDeclarationOrigin_of_mem declaration.2

/-- Static colour retained by the unique rho generated-declaration origin. -/
def RhoCostAuthoredGeneratorOrigin.color
    {left right : Pattern}
    {witness :
      ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
        rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
          rhoCIGSLT.costWholeLanguage left right} :
    RhoCostAuthoredGeneratorOrigin witness → CostStaticColor :=
  match witness with
  | .core (.equation _ instanceWitness) =>
      match instanceWitness with
      | .forward _ _ _ _ _ _ _ => fun origin =>
          RhoCostEquationDeclarationOrigin.color origin
      | .reverse _ _ _ _ _ _ _ => fun origin =>
          RhoCostEquationDeclarationOrigin.color origin
  | .reflective _ _ _ => fun origin =>
      RhoCostReflectiveDeclarationOrigin.color origin

/-- Typed rho Cost occurrence with its exact unique rho declaration origin.
This strengthens the generic carrier from an arbitrary authored source
declaration to rho's sole QuoteDrop equation or reflective presentation. -/
structure RhoCostTypedGeneratorOccurrence
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {left right : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree targetBound targetSort}
    (generator : ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage targetFree targetBound (.base targetSort.1)
      left right) where
  witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
    rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left.1 right.1
  erasesTo : witness.erase = generator
  origin : RhoCostAuthoredGeneratorOrigin witness

/-- Every typed generated rho Cost edge has an exact base-or-wrapped
QuoteDrop occurrence above it. -/
theorem nonempty_rhoCostTypedGeneratorOccurrence
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {left right : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree targetBound targetSort}
    (generator : ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage targetFree targetBound (.base targetSort.1)
      left right) :
    Nonempty (RhoCostTypedGeneratorOccurrence generator) := by
  obtain ⟨witness, erasesTo⟩ :=
    ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness.exists_erasing_to
      generator
  obtain ⟨origin⟩ := nonempty_rhoCostAuthoredGeneratorOrigin witness
  exact ⟨⟨witness, erasesTo, origin⟩⟩

namespace RhoCostTypedGeneratorOccurrence

/-- Exact static colour of the unique generated rho declaration. -/
def declarationColor
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {left right : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree targetBound targetSort}
    {generator : ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage targetFree targetBound (.base targetSort.1)
      left right}
    (occurrence : RhoCostTypedGeneratorOccurrence generator) :
    CostStaticColor := occurrence.origin.color

end RhoCostTypedGeneratorOccurrence

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
