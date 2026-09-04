import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- PREDICTION: the empty parallel canonicalizes to the unit constructor. -/
example :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
      (.collection
        rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        [] none) =
      .apply rhoReflectivePresentation.parallelUnitConstructor [] := by
  simp [canonicalize, canonicalizeList, normalizeParallelElements,
    collapseParallel, Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
