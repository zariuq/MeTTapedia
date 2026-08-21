import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalCollapse
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyedTyping

/-!
# Quote-collapse exclusion from reflective scope safety

Reflective canonicalization may erase a Quote/Drop shell, but a quotation
whose body satisfies the quote-aware binder-safety invariant cannot thereby
expose a bare bound variable.  The proof combines collapse inversion with the
scope-preservation theorem for ordinary canonicalization.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-- A quote application satisfying the quote's own sealing invariant cannot
canonicalize to a bare bound variable.  Any such collapse would require a
sole argument whose canonical form is a drop around that bound variable; at
quote depth zero this contradicts preservation of binder safety. -/
theorem canonicalize_quote_ne_bvar_of_binderSafeAt
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (safetyDepth : Nat) (arguments : List Pattern) (index : Nat)
    (safe : binderSafeAt declaration.quoteConstructor safetyDepth
      (.apply declaration.quoteConstructor arguments) = true) :
    canonicalize declaration (.apply declaration.quoteConstructor arguments) ≠
      .bvar index := by
  intro canonical
  rw [canonicalize_apply_eq_finish] at canonical
  rcases finishNormalizeReflectiveApply_quote_cases declaration
      (arguments.map (canonicalize declaration)) with
    ⟨inner, mappedEq, resultEq⟩ | resultEq
  · rw [resultEq] at canonical
    cases arguments with
    | nil => simp at mappedEq
    | cons argument arguments =>
        cases arguments with
        | nil =>
            have argumentCanonical : canonicalize declaration argument =
                .apply declaration.dropConstructor [inner] := by
              simpa using mappedEq
            have argumentSafe : binderSafeAt declaration.quoteConstructor 0
                argument = true := by
              simpa [binderSafeAt] using safe
            have normalizedSafe := canonicalize_binderSafeAt declaration
              declaration.quoteConstructor 0 argument argumentSafe
            have dropNeQuote : declaration.dropConstructor ≠
                declaration.quoteConstructor := Ne.symm quoteNeDrop
            have dropDecision :
                (declaration.dropConstructor ==
                  declaration.quoteConstructor) = false :=
              beq_eq_false_iff_ne.mpr dropNeQuote
            rw [argumentCanonical, canonical] at normalizedSafe
            simp [binderSafeAt, binderSafeListAt, dropDecision] at normalizedSafe
        | cons second rest => simp at mappedEq
  · rw [resultEq] at canonical
    cases canonical

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
