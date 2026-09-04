import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorProCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem proErase_constructor_basePDrop :
    proEraseConstructor (costBaseConstructorName "PDrop") = "PDrop" := by decide

theorem proErase_constructor_wrappedPDrop :
    proEraseConstructor (costWrappedConstructorName "PDrop") = "PDrop" := by
  decide

/-- Both endpoints erase to the authored double shell. -/
theorem proErase_proLeft :
    proErase proLeft =
      .apply "NQuote" [.apply "PDrop" [.apply "NQuote"
        [.apply "PZero" []]]] := by
  simp [proLeft, proErase, proErase_constructor_baseQuote,
    proErase_constructor_basePDrop, proErase_constructor_wrappedQuote,
    proErase_constructor_wrappedZero]

theorem proErase_proRight :
    proErase proRight =
      .apply "NQuote" [.apply "PDrop" [.apply "NQuote"
        [.apply "PZero" []]]] := by
  simp [proRight, proErase, proErase_constructor_wrappedQuote,
    proErase_constructor_wrappedPDrop, proErase_constructor_baseQuote,
    proErase_constructor_baseZero]

/-- The foreign-colour endpoints are rigid: the base canonicalizer cannot see
the wrapped redex, and conversely. -/
theorem proRight_canonical_base :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl) proRight =
      proRight := by decide

theorem proLeft_canonical_wrapped :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
        rhoReflectivePresentation.toReflectivePresentationDecl) proLeft =
      proLeft := by decide

/-- The authored canonicalizer fires on the erased double shell. -/
theorem authored_canonical_doubleShell :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        (.apply "NQuote" [.apply "PDrop" [.apply "NQuote"
          [.apply "PZero" []]]]) =
      .apply "NQuote" [.apply "PZero" []] := by decide

/-- **The erasure square holds on the canary's own-colour endpoint.** -/
theorem erasureSquare_holds_proLeft_base :
    proErase (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT .base
          rhoReflectivePresentation.toReflectivePresentationDecl) proLeft) =
      canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        (proErase proLeft) := by
  rw [proLeft_canonical_base, proErase_proLeft,
    authored_canonical_doubleShell]
  simp [proErase, proErase_constructor_wrappedQuote,
    proErase_constructor_wrappedZero]

/-- **The erasure square FAILS on the canary's foreign-colour endpoint.**
The base canonicalizer is blind to the wrapped redex, so erasure exposes a
quote-drop pair the left leg never fired: LHS `Q(D(Q(0)))`, RHS `Q(0)`.

Consequence: in the fibration square `U ∘ H_C ≅ H ∘ U`, `H_C` can NOT be the
single-colour canonicalizer.  Only the hereditary normalizer — which descends
through foreign boundaries — is a candidate. -/
theorem erasureSquare_fails_proRight_base :
    proErase (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT .base
          rhoReflectivePresentation.toReflectivePresentationDecl) proRight) ≠
      canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        (proErase proRight) := by
  rw [proRight_canonical_base, proErase_proRight,
    authored_canonical_doubleShell]
  decide

/-- The mirror failure at the wrapped declaration, on the other endpoint. -/
theorem erasureSquare_fails_proLeft_wrapped :
    proErase (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation.toReflectivePresentationDecl) proLeft) ≠
      canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        (proErase proLeft) := by
  rw [proLeft_canonical_wrapped, proErase_proLeft,
    authored_canonical_doubleShell]
  decide

/-- **Pro's equation (4.1) instance: on the SINGLE-COLOUR image the square is
exact.**  `canonicalize_c (Color_c p) = Color_c (canonicalize_AUTH p)` for the
authored double-shell `Q(D(Q(0)))` at both colours. -/
theorem colour_canonicalize_commutes_on_image (color : CostStaticColor) :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (mapPattern (color.symbols rhoCIGSLT)
          (.apply "NQuote" [.apply "PDrop" [.apply "NQuote"
            [.apply "PZero" []]]])) =
      mapPattern (color.symbols rhoCIGSLT)
        (canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
          (.apply "NQuote" [.apply "PDrop" [.apply "NQuote"
            [.apply "PZero" []]]])) := by
  cases color <;> decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
