import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- The external review's depth-three cross-colour canary, left endpoint:
`Q_b(D_b(Q_w(0_w)))`. -/
def proLeft : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop")
      [.apply (costWrappedConstructorName "NQuote")
        [.apply (costWrappedConstructorName "PZero") []]]]

/-- Right endpoint: `Q_w(D_w(Q_b(0_b)))`. -/
def proRight : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop")
      [.apply (costBaseConstructorName "NQuote")
        [.apply (costBaseConstructorName "PZero") []]]]

/-- **Each endpoint collapses at its own colour and is rigid at the other.** -/
theorem proLeft_canonical_base :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl) proLeft =
      .apply (costWrappedConstructorName "NQuote")
        [.apply (costWrappedConstructorName "PZero") []] := by decide

theorem proRight_canonical_wrapped :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
        rhoReflectivePresentation.toReflectivePresentationDecl) proRight =
      .apply (costBaseConstructorName "NQuote")
        [.apply (costBaseConstructorName "PZero") []] := by decide

/-- **The canary is NOT canonically equal at the base declaration.** -/
theorem proPair_not_canonical_base :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl) proLeft ≠
      canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl) proRight := by
  decide

/-- **Nor at the wrapped declaration.** -/
theorem proPair_not_canonical_wrapped :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
        rhoReflectivePresentation.toReflectivePresentationDecl) proLeft ≠
      canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
        rhoReflectivePresentation.toReflectivePresentationDecl) proRight := by
  decide

/-- **Consequence: the canary does not satisfy the premise of our cross-colour
obligation at either colour.**  Our obligations are premised on single-colour
canonical equality; this witness fails that premise on both sides, so it
refutes a statement premised on authored (colour-erased) equality, not ours. -/
theorem proPair_outside_our_premise (color : CostStaticColor) :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl) proLeft ≠
      canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl) proRight := by
  cases color
  · exact proPair_not_canonical_base
  · exact proPair_not_canonical_wrapped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
