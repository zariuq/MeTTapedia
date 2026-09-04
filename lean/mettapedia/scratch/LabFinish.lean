import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PROBE: a non-quote application head survives the finisher. -/
example (declaration : ReflectivePresentationDecl) (constructor : String)
    (arguments : List Pattern)
    (notQuote : constructor ≠ declaration.quoteConstructor) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
      declaration constructor arguments = .apply constructor arguments := by
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
  simp [notQuote]

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
