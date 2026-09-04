import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **A non-quote application head survives keyed canonicalization.** -/
theorem canonicalizeByDepths_apply_of_ne_quote {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (constructor : String)
    (arguments : List Pattern)
    (notQuote : constructor ≠ declaration.quoteConstructor) :
    canonicalizeByDepths key declaration availableDepth scopeDepth
        (.apply constructor arguments) =
      .apply constructor
        (canonicalizeListByDepths key declaration availableDepth scopeDepth
          arguments) := by
  unfold canonicalizeByDepths
  simp only [beq_iff_eq, notQuote, if_false]
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
  simp [notQuote]

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
