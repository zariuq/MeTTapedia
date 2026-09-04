import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- PREDICTION: quote(drop(x)) collapses to x. -/
example (name : String) :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
      (.apply
        rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
        [.apply
          rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor
          [.fvar name]]) = .fvar name := by
  simp [canonicalize, canonicalizeList,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
