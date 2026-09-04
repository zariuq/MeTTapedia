import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- PREDICTION A: a singleton parallel canonicalizes to its element. -/
example (name : String) :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
      (.collection
        rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        [.fvar name] none) = .fvar name := by
  simp [canonicalize, canonicalizeList, normalizeParallelElements,
    collapseParallel, parallelSplice,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns]

/-- PREDICTION B: a bare quote does NOT collapse — quote-drop needs a PDrop
argument, so the context does not evaporate. -/
example (name : String) :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
      (.apply
        rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
        [.fvar name]) ≠ .fvar name := by
  simp [canonicalize, canonicalizeList, Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
