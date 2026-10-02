import Mettapedia.GSLT.LanguageDef.BindingSignatureEquationPresentation
import Mettapedia.GSLT.LanguageDef.CostInteractionClosure
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafProgramModel
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-!
# Actual generated rho equation rows in the binding quotient

Both static QuoteDrop copies are compiled from the authored Cost language.
The existing contextual quotient supplies their full binding model and its
operational presheaf interpretation. Collection algebra metadata is a separate
part of the source theory and is not inserted into this two-row presentation.

The open schema name is an explicit equation parameter. Instantiating it may
enter the schema's quotation constructor. Reflective receiver substitution
instead acts on bound object variables and seals literal quotations; the two
operations are checked separately below.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedEquationPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.EquationPresentation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

abbrev language := rhoCIGSLT.costWholeLanguage

def sourceEquation : Equation := rhoCalc.equations[0]

def baseEquation : Equation := costBaseEquationDecl sourceEquation

def wrappedEquation : Equation := costWrappedEquationDecl rhoCIGSLT.theory sourceEquation

def nameSort : TypeExpr := .base (costBaseSortName "Name")

theorem base_compiles : (compile? language baseEquation nameSort).isSome = true := by
  decide +kernel

theorem wrapped_compiles : (compile? language wrappedEquation nameSort).isSome = true := by
  decide +kernel

def baseRow : CompiledRow language baseEquation nameSort :=
  (compile? language baseEquation nameSort).get base_compiles

def wrappedRow : CompiledRow language wrappedEquation nameSort :=
  (compile? language wrappedEquation nameSort).get wrapped_compiles

/-- These are all the explicit equation rows in this actual generated language.
The declaration's parallel collection algebra remains separately specified. -/
theorem declared_rows : language.equations = [baseEquation, wrappedEquation] := rfl

def equations : List (EqAxiom (signatureOf language) []) :=
  [baseRow.toAxiom, wrappedRow.toAxiom]

/-- Every operator retains its actual binding arity in the quotient clone. -/
noncomputable abbrev algebra := BindingEquationQuotientModel.algebra equations

theorem full_contextual_satisfaction :
    BindingEquationInterpretation.Satisfies algebra equations :=
  BindingEquationQuotientModel.algebra_satisfies equations

/-- This supplies the existing presheaf classifier with a constructed model. -/
noncomputable def presheafInterpretation :=
  IntrinsicScopedOperationalPresheafProgramModel.quotientSatisfyingInterpretation equations

theorem base_named_readback :
    OpenReification.namedFirstOrderErase?
        (NamedFreeContext.names baseEquation.typeContext) baseRow.left =
      some baseEquation.left ∧
    OpenReification.namedFirstOrderErase?
        (NamedFreeContext.names baseEquation.typeContext) baseRow.right =
      some baseEquation.right := ⟨baseRow.left_named, baseRow.right_named⟩

theorem wrapped_named_readback :
    OpenReification.namedFirstOrderErase?
        (NamedFreeContext.names wrappedEquation.typeContext) wrappedRow.left =
      some wrappedEquation.left ∧
    OpenReification.namedFirstOrderErase?
        (NamedFreeContext.names wrappedEquation.typeContext) wrappedRow.right =
      some wrappedEquation.right := ⟨wrappedRow.left_named, wrappedRow.right_named⟩

/-- Applying a schema binding instantiates N even below the schema quotation. -/
theorem schema_instantiation_enters_quote (replacement : Pattern) :
    applyBindings [(costSourceSchemaName "N", replacement)] baseEquation.left =
      .apply (costBaseConstructorName "NQuote")
        [.apply (costBaseConstructorName "PDrop") [replacement]] := by
  change applyBindings [(costSourceSchemaName "N", replacement)]
      (.apply (costBaseConstructorName "NQuote")
        [.apply (costBaseConstructorName "PDrop")
          [.fvar (costSourceSchemaName "N")]]) = _
  simp [applyBindings]

def baseReflection :=
  costBaseReflectivePresentationDecl rhoReflectivePresentation.toReflectivePresentationDecl

def sealedBody : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "POutput")
      [.bvar 0, .apply (costBaseConstructorName "PZero") []]]

/-- The same bound object position inside literal code is sealed against
ordinary reflective receiver substitution. -/
theorem ambient_substitution_seals_quote (replacement : Pattern) :
    substituteReflective baseReflection 0 replacement sealedBody = sealedBody := by
  rfl

/-- Sealing is observably different from entering the quoted body. -/
theorem sealed_substitution_not_body_replacement :
    substituteReflective baseReflection 0 (.fvar "replacement") sealedBody ≠
      .apply (costBaseConstructorName "NQuote")
        [.apply (costBaseConstructorName "POutput")
          [.fvar "replacement", .apply (costBaseConstructorName "PZero") []]] := by
  rw [ambient_substitution_seals_quote]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedEquationPresentation
