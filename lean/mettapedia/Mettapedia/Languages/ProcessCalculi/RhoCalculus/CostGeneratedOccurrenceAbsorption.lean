import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratedOccurrence

/-!
# Reflective absorption of generated rho Cost occurrences

The generated Cost equation and reflective tables remain distinct occurrence
sources.  Nevertheless, every exact rho occurrence selects a generated
reflective declaration whose canonicalizer already identifies the retained
redex and contractum.  This is the occurrence-local half of the later
selected-versus-foreign region classifier.

No region colour is guessed here.  The certificate retains the exact
generated reflective declaration and its authored rho origin; a later
alignment compares that declaration colour with the selected static frame.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A proof-relevant generated rho occurrence is absorbed locally by one
exact generated reflective declaration.

The indexed occurrence still records whether the original justification was
an equation instance or a reflective equality.  The added declaration is
therefore a normalization witness, not a replacement provenance source. -/
structure RhoCostGeneratorAbsorption
    {left right : Pattern}
    (witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right) where
  declaration : { declaration : ReflectivePresentationDecl //
    declaration ∈ rhoCIGSLT.costWholeReflectionProfile.presentations }
  origin : RhoCostReflectiveDeclarationOrigin declaration.1
  representatives :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration.1
        witness.redex =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration.1
        witness.contractum

namespace RhoCostGeneratorAbsorption

/-- Static colour of the exact reflective declaration that absorbs the
retained occurrence. -/
def color
    {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right}
    (absorption : RhoCostGeneratorAbsorption witness) : CostStaticColor :=
  absorption.origin.color

/-- The absorbing declaration is exactly the indicated static image of
rho's sole reflective presentation. -/
theorem declaration_eq
    {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right}
    (absorption : RhoCostGeneratorAbsorption witness) :
    absorption.declaration.1 =
      costStaticReflectivePresentationDecl rhoCIGSLT absorption.color
        rhoReflectivePresentation.toReflectivePresentationDecl :=
  absorption.origin.target_eq

/-- Local absorption extends through the exact one-hole context retained by
the authored occurrence.  This is the full-endpoint representative equality
needed by paired hereditary elaboration; equation/reflection provenance stays
in the indexed witness rather than being reconstructed from the equality. -/
theorem contextualRepresentatives
    {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right}
    (absorption : RhoCostGeneratorAbsorption witness) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        absorption.declaration.1 left =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        absorption.declaration.1 right := by
  cases witness with
  | core witness =>
      cases witness with
      | equation context instanceWitness =>
          exact ReflectiveEquationSemantics.canonicalize_fill_congr
            absorption.declaration.1 context absorption.representatives
  | reflective context declaration representatives =>
      exact ReflectiveEquationSemantics.canonicalize_fill_congr
        absorption.declaration.1 context absorption.representatives

end RhoCostGeneratorAbsorption

/-- A proof-relevant generated Quote/Drop equation instance is absorbed by
the generated reflective declaration of the very same retained colour.

Unlike the proposition-valued table-agreement theorem, this statement is
indexed by `RhoCostEquationInstanceOrigin`.  It can therefore be used when
constructing a Type-valued generator-alignment certificate without choosing
provenance from an erased existential. -/
theorem rhoCostEquationInstanceOrigin_representatives
    {redex contractum : Pattern}
    (witness : EquationSemantics.DeclaredEquationInstanceWitness
      defaultBasePremises rhoCIGSLT.costWholeLanguage redex contractum)
    (origin : RhoCostEquationInstanceOrigin witness) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT
          (RhoCostEquationInstanceOrigin.color origin)
          rhoReflectivePresentation.toReflectivePresentationDecl) redex =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT
          (RhoCostEquationInstanceOrigin.color origin)
          rhoReflectivePresentation.toReflectivePresentationDecl)
        contractum := by
  cases witness with
  | forward fuel equation initialBindings finalBindings matched premises
      target_eq =>
      rcases origin with ⟨color, equation_eq⟩
      change Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) redex =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) contractum
      have matched' : initialBindings ∈
          matchPattern
            (costStaticEquationDecl rhoCIGSLT color rhoCalc.equations[0]).left
            redex := by
        simpa only [equation_eq] using matched
      have premises' : PremisesAt defaultBasePremises
          rhoCIGSLT.costWholeLanguage fuel initialBindings
          (costStaticEquationDecl rhoCIGSLT color
            rhoCalc.equations[0]).premises finalBindings := by
        simpa only [equation_eq] using premises
      have target_eq' :
          applyBindings finalBindings
              (costStaticEquationDecl rhoCIGSLT color
                rhoCalc.equations[0]).right = contractum := by
        simpa only [equation_eq] using target_eq
      have premisesEmpty :
          (costStaticEquationDecl rhoCIGSLT color
            rhoCalc.equations[0]).premises = [] := by
        apply costStaticEquationDecl_premises
        rfl
      rw [premisesEmpty] at premises'
      cases premises'
      have matchCorrect : Pattern.isMatchCorrect
          (costStaticEquationDecl rhoCIGSLT color
            rhoCalc.equations[0]).left = true := by
        cases color <;> decide
      have source_eq := matchPattern_correct matched' matchCorrect
      rw [← source_eq, ← target_eq']
      cases color <;>
        simp [rhoCalc, rhoReflectivePresentation, costStaticEquationDecl,
          costBaseEquationDecl, costWrappedEquationDecl, costBaseEquation,
          costWrappedEquation, mapEquationSchemaNames, mapEquation,
          mapPatternListSchemaNames, mapPatternSchemaNames, mapPattern,
          applyBindings, costStaticReflectivePresentationDecl,
          costBaseReflectivePresentationDecl,
          costWrappedReflectivePresentationDecl, mapReflectivePresentation,
          costBaseLanguageDefSymbolMap, costBaseStaticReflectiveSymbols,
          costWrappedStaticReflectiveSymbols, costBaseStaticSymbols,
          costWrappedStaticSymbols, costBaseConstructorName,
          costWrappedConstructorName, costBaseConstructorTag,
          costWrappedConstructorTag,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]
  | reverse fuel equation initialBindings finalBindings matched premises
      target_eq =>
      rcases origin with ⟨color, equation_eq⟩
      change Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) redex =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) contractum
      have matched' : initialBindings ∈
          matchPattern
            (costStaticEquationDecl rhoCIGSLT color rhoCalc.equations[0]).right
            redex := by
        simpa only [equation_eq] using matched
      have premises' : PremisesAt defaultBasePremises
          rhoCIGSLT.costWholeLanguage fuel initialBindings
          (costStaticEquationDecl rhoCIGSLT color
            rhoCalc.equations[0]).premises finalBindings := by
        simpa only [equation_eq] using premises
      have target_eq' :
          applyBindings finalBindings
              (costStaticEquationDecl rhoCIGSLT color
                rhoCalc.equations[0]).left = contractum := by
        simpa only [equation_eq] using target_eq
      have premisesEmpty :
          (costStaticEquationDecl rhoCIGSLT color
            rhoCalc.equations[0]).premises = [] := by
        apply costStaticEquationDecl_premises
        rfl
      rw [premisesEmpty] at premises'
      cases premises'
      have matchCorrect : Pattern.isMatchCorrect
          (costStaticEquationDecl rhoCIGSLT color
            rhoCalc.equations[0]).right = true := by
        cases color <;> decide
      have source_eq := matchPattern_correct matched' matchCorrect
      rw [← source_eq, ← target_eq']
      cases color <;>
        simp [rhoCalc, rhoReflectivePresentation, costStaticEquationDecl,
          costBaseEquationDecl, costWrappedEquationDecl, costBaseEquation,
          costWrappedEquation, mapEquationSchemaNames, mapEquation,
          mapPatternListSchemaNames, mapPatternSchemaNames, mapPattern,
          applyBindings, costStaticReflectivePresentationDecl,
          costBaseReflectivePresentationDecl,
          costWrappedReflectivePresentationDecl, mapReflectivePresentation,
          costBaseLanguageDefSymbolMap, costBaseStaticReflectiveSymbols,
          costWrappedStaticReflectiveSymbols, costBaseStaticSymbols,
          costWrappedStaticSymbols, costBaseConstructorName,
          costWrappedConstructorName, costBaseConstructorTag,
          costWrappedConstructorTag,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

/-- Construct local reflective absorption directly from the exact retained
rho declaration origin.  Equation and reflection stay distinguishable in the
indexed witness, while both branches expose their matching coloured
reflective representative equality. -/
def rhoCostGeneratorAbsorptionOfOrigin
    {left right : Pattern}
    (witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right)
    (origin : RhoCostAuthoredGeneratorOrigin witness) :
    RhoCostGeneratorAbsorption witness :=
  match witness, origin with
  | .core (.equation context instanceWitness), equationOrigin =>
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
        equationOrigin.color
          rhoReflectivePresentation.toReflectivePresentationDecl
      { declaration := ⟨declaration, by
          exact costStaticReflectivePresentationDecl_mem rhoCIGSLT
            equationOrigin.color
            rhoReflectivePresentation.toReflectivePresentationDecl (by
              change rhoReflectivePresentation.toReflectivePresentationDecl ∈
                rhoReflectionProfile.presentations
              simp [rhoReflectionProfile])⟩
        origin :=
          ⟨equationOrigin.color, rfl⟩
        representatives :=
          rhoCostEquationInstanceOrigin_representatives instanceWitness
            equationOrigin }
  | .reflective context declaration representatives, reflectiveOrigin =>
      { declaration := declaration
        origin := reflectiveOrigin
        representatives := representatives }

namespace RhoCostTypedGeneratorOccurrence

/-- Recover the exact local reflective absorber from the occurrence's
retained rho declaration origin.  No proposition-valued declaration search
or choice is performed. -/
def absorption
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
    RhoCostGeneratorAbsorption occurrence.witness :=
  rhoCostGeneratorAbsorptionOfOrigin occurrence.witness occurrence.origin

end RhoCostTypedGeneratorOccurrence

/-- Relative position of an exact generated rho declaration with respect to
one selected static region colour.

This certificate records only the exhaustive two-colour split.  In
particular, the `foreign` constructor does not assert that the occurrence is
semantically harmless; that requires the subsequent parallel-structure
absorption theorem. -/
inductive RhoCostDeclarationRegionPosition
    {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right}
    (absorption : RhoCostGeneratorAbsorption witness)
    (regionColor : CostStaticColor) : Type where
  | selected (same : absorption.color = regionColor) :
      RhoCostDeclarationRegionPosition absorption regionColor
  | foreign (opposite : absorption.color = regionColor.flip) :
      RhoCostDeclarationRegionPosition absorption regionColor

namespace RhoCostDeclarationRegionPosition

/-- The two generated static colours make declaration position decidable and
exhaustive without inspecting syntax or typing evidence. -/
def classify
    {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right}
    (absorption : RhoCostGeneratorAbsorption witness)
    (regionColor : CostStaticColor) :
    RhoCostDeclarationRegionPosition absorption regionColor := by
  by_cases same : absorption.color = regionColor
  · exact .selected same
  · exact .foreign (CostStaticColor.eq_flip_of_ne (Ne.symm same))

/-- A selected certificate exposes equality with the region's exact generated
reflective declaration. -/
theorem declaration_eq_of_selected
    {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right}
    {absorption : RhoCostGeneratorAbsorption witness}
    {regionColor : CostStaticColor}
    (same : absorption.color = regionColor) :
    absorption.declaration.1 =
      costStaticReflectivePresentationDecl rhoCIGSLT regionColor
        rhoReflectivePresentation.toReflectivePresentationDecl := by
  rw [← same]
  exact absorption.declaration_eq

/-- A foreign certificate exposes the unique opposite generated reflective
declaration, without yet claiming semantic absorption by the selected
region. -/
theorem declaration_eq_of_foreign
    {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right}
    {absorption : RhoCostGeneratorAbsorption witness}
    {regionColor : CostStaticColor}
    (opposite : absorption.color = regionColor.flip) :
    absorption.declaration.1 =
      costStaticReflectivePresentationDecl rhoCIGSLT regionColor.flip
        rhoReflectivePresentation.toReflectivePresentationDecl := by
  rw [← opposite]
  exact absorption.declaration_eq

end RhoCostDeclarationRegionPosition

/-- Every exact generated rho occurrence has a local generated-reflective
absorption certificate.  Ordinary equation occurrences are converted through
the already-proved Quote/Drop table agreement; reflective occurrences retain
their authored representative equality directly. -/
theorem nonempty_rhoCostGeneratorAbsorption
    {left right : Pattern}
    (witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right) :
    Nonempty (RhoCostGeneratorAbsorption witness) := by
  cases witness with
  | core witness =>
      cases witness with
      | equation context instanceWitness =>
          obtain ⟨fuel, bounded⟩ := instanceWitness.erase
          obtain ⟨declaration, membership, representatives⟩ :=
            rho_costEquationInstanceAt_canonicalize_eq bounded
          obtain ⟨origin⟩ :=
            nonempty_rhoCostReflectiveDeclarationOrigin_of_mem membership
          exact ⟨⟨⟨declaration, membership⟩, origin, representatives⟩⟩
  | reflective context declaration representatives =>
      obtain ⟨origin⟩ :=
        nonempty_rhoCostReflectiveDeclarationOrigin_of_mem declaration.2
      exact ⟨⟨declaration, origin, representatives⟩⟩

/-- Typed occurrence coverage specializes the local absorption theorem
without forgetting the indexed open fibre or the original declaration
provenance. -/
theorem nonempty_rhoCostTypedGeneratorAbsorption
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
    Nonempty (RhoCostGeneratorAbsorption occurrence.witness) :=
  nonempty_rhoCostGeneratorAbsorption occurrence.witness

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
