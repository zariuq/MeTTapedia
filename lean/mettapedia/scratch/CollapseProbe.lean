import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

example (declarationColor : CostStaticColor) (index : Nat) :
    canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).parallelCollection
        [.bvar index] none) = .bvar index := by
  rw [canonicalize_parallel_singleton, canonicalize]

example (declarationColor : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation).dropConstructor ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation).quoteConstructor := by
  cases declarationColor <;> decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
