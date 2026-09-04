import Mettapedia.GSLT.LanguageDef.CostRestorationApexSymm
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratedOccurrence

/-!
# Equation instances collapse at one endpoint, and the rho quote heads are
exactly two

Two boundary facts for the universal typed apex recursion.

First, every proof-relevant instance of a generated rho equation exposes a
collapsing root on one endpoint: the sole authored equation is the
Quote/Drop law, whose non-variable template side is quote-headed, so a
forward instance has a quote-headed redex and a reverse instance a
quote-headed contractum.  The equation branch of the generator classifier
therefore always reaches the shape-agnostic bridge side of the root
dichotomy and never needs its own congruence recursion.

Second, the language-level quote heads of the generated rho Cost language
are exactly the two colour copies of `NQuote`.  Together with the aligned
arms this makes the apply-head dispatch of the apex recursion exhaustive by
name.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A successful match against a rigid application template forces the term
to be an application with the same head. -/
theorem matchPattern_apply_shape {constructor : String}
    {templateArguments : List Pattern}
    {bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
    {term : Pattern}
    (matched : bindings ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern
      (.apply constructor templateArguments) term) :
    ∃ termArguments, term = .apply constructor termArguments := by
  cases term with
  | apply termConstructor termArguments =>
      simp only [Mettapedia.OSLF.MeTTaIL.Match.matchPattern] at matched
      split at matched
      case isTrue condition =>
        simp only [Bool.and_eq_true] at condition
        obtain ⟨headEq, -⟩ := condition
        exact ⟨termArguments, by rw [eq_of_beq headEq]⟩
      case isFalse =>
        simp at matched
  | bvar index =>
      simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern] at matched
  | fvar name =>
      simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern] at matched
  | lambda binder body =>
      simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern] at matched
  | multiLambda arity binders body =>
      simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern] at matched
  | subst body replacement =>
      simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern] at matched
  | collection collectionType elements rest =>
      simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern] at matched

/-- Every proof-relevant instance of a generated rho equation has a
collapsing (quote-headed) endpoint at its own colour: the redex for a
forward instance, the contractum for a reverse instance. -/
theorem rho_costEquationInstance_collapsingEndpoint
    {redex contractum : Pattern}
    (witness : EquationSemantics.DeclaredEquationInstanceWitness
      defaultBasePremises rhoCIGSLT.costWholeLanguage redex contractum) :
    ∃ color : CostStaticColor,
      CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) redex ∨
        CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          contractum := by
  cases witness with
  | forward fuel equation initialBindings finalBindings matched premises
      target_eq =>
      obtain ⟨origin⟩ :=
        nonempty_rhoCostEquationDeclarationOrigin_of_mem equation.2
      obtain ⟨color, declarationEq⟩ := origin
      refine ⟨color, Or.inl ?_⟩
      have leftShape : ∃ innerArguments, equation.1.left =
          .apply (ReflectivePresentationDecl.quoteConstructor
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl))
            innerArguments := by
        rw [declarationEq]
        cases color <;> exact ⟨_, rfl⟩
      obtain ⟨innerArguments, leftEq⟩ := leftShape
      rw [leftEq] at matched
      obtain ⟨termArguments, redexEq⟩ := matchPattern_apply_shape matched
      exact Or.inl ⟨termArguments, redexEq⟩
  | reverse fuel equation initialBindings finalBindings matched premises
      target_eq =>
      obtain ⟨origin⟩ :=
        nonempty_rhoCostEquationDeclarationOrigin_of_mem equation.2
      obtain ⟨color, declarationEq⟩ := origin
      refine ⟨color, Or.inr ?_⟩
      have leftShape : ∃ innerArguments, equation.1.left =
          .apply (ReflectivePresentationDecl.quoteConstructor
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl))
            innerArguments := by
        rw [declarationEq]
        cases color <;> exact ⟨_, rfl⟩
      obtain ⟨innerArguments, leftEq⟩ := leftShape
      rw [leftEq] at target_eq
      exact Or.inl ⟨innerArguments.map
        (Mettapedia.OSLF.MeTTaIL.Match.applyBindings finalBindings), by
          rw [← target_eq]
          simp [Mettapedia.OSLF.MeTTaIL.Match.applyBindings]⟩

/-- The language-level quote heads of the generated rho Cost language are
exactly the two colour copies of `NQuote`. -/
theorem rho_isQuoteConstructor_cases {constructor : String}
    (isQuote : ReflectiveContextSupport.isQuoteConstructor
      rhoCIGSLT.costWholeReflectionProfile constructor = true) :
    constructor = costBaseConstructorName "NQuote" ∨
      constructor = costWrappedConstructorName "NQuote" := by
  unfold ReflectiveContextSupport.isQuoteConstructor at isQuote
  rw [CIGSLT.costWholeReflectionProfile_presentations] at isQuote
  have tableShape : rhoCIGSLT.costStaticReflectivePresentations =
      [costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl,
       costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
        rhoReflectivePresentation.toReflectivePresentationDecl] := by
    rfl
  rw [tableShape] at isQuote
  simp only [List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at isQuote
  rcases isQuote with baseCase | wrappedCase
  · exact Or.inl baseCase.symm
  · exact Or.inr wrappedCase.symm

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
