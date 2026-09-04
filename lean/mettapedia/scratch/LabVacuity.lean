import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorFlat

/-! LAB: is the CROSS-COLOUR collapsing arm forced into one orientation?
    H: with leftColor ≠ rightColor, Name-fibre views, and the collapsing
       disjunction, declarationColor equals EXACTLY ONE of the two colours —
       so "the collapsing side is the declaration-coloured side" is forced. -/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

example {declarationColor leftColor rightColor : CostStaticColor}
    {leftArguments rightArguments : List Pattern}
    (different : leftColor ≠ rightColor)
    (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply ((leftColor.symbols rhoCIGSLT).constructor "NQuote")
          leftArguments) ∨
      CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply ((rightColor.symbols rhoCIGSLT).constructor "NQuote")
          rightArguments)) :
    (declarationColor = leftColor ∧ declarationColor ≠ rightColor) ∨
    (declarationColor = rightColor ∧ declarationColor ≠ leftColor) := by
  rcases rhoCrossColorNameFibre_declarationColor_eq collapsing with h | h
  · exact Or.inl ⟨h, fun bad => different (h ▸ bad ▸ rfl)⟩
  · exact Or.inr ⟨h, fun bad => different (bad ▸ h ▸ rfl)⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
