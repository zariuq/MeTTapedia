import Mettapedia.GSLT.LanguageDef.RegexCharacterInterpretation
import Mettapedia.Computability.RegularLanguages.ObservationTable

/-!
# The observation table by the authored rules

The rows of the profile's observation table that concern whole-word matching,
nullability and the derivative are observations of the authored rules: each
is a step of the declared rewrite relation from the encoded request.

The authored derivative rules do not simplify. For the row that lists the
derivative of `a+` by `a` as `a*`, the authored rules produce the
concatenation of the empty word with `a*`, and they do not produce `a*`. The
rows for search and replacement have no authored request: the theory declares
no constructor for them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexObservationTable

open Mettapedia.Computability.RegularLanguages
open Mettapedia.Computability.RegularLanguages.ObservationTable
open RegexCharacterInterpretation

/-- Decide an authored whole-word observation by the matcher. -/
theorem authored_step_of_fullMatch (p : Regex Char) (input : String) :
    RegexTheory.Step (compiled p input) (RegexTheory.boolean (fullMatch p input.toList)) := by
  cases result : fullMatch p input.toList with
  | true => exact (authored_accepts_iff p input).mpr ((fullMatch_correct _ _).mp result)
  | false =>
      refine (authored_rejects_iff p input).mpr fun member => ?_
      rw [(fullMatch_correct _ _).mpr member] at result
      cases result

/-- Row M1. -/
theorem authored_accepts_abcb :
    RegexTheory.Step (compiled aThenBsOrCs "abcb") (RegexTheory.boolean true) :=
  accepts_abcb ▸ authored_step_of_fullMatch aThenBsOrCs "abcb"

/-- Row M2. -/
theorem authored_rejects_ax :
    RegexTheory.Step (compiled aThenBsOrCs "ax") (RegexTheory.boolean false) :=
  rejects_ax ▸ authored_step_of_fullMatch aThenBsOrCs "ax"

/-- Row M3. -/
theorem authored_rejects_xab :
    RegexTheory.Step (compiled aThenBsOrCs "xab") (RegexTheory.boolean false) :=
  rejects_xab_although_found.1 ▸ authored_step_of_fullMatch aThenBsOrCs "xab"

/-- The authored rules do not also accept the rejected word. -/
theorem authored_does_not_accept_xab :
    ¬ RegexTheory.Step (compiled aThenBsOrCs "xab") (RegexTheory.boolean true) := by
  intro step
  have output := authored_output_eq aThenBsOrCs "xab" _ step
  rw [rejects_xab_although_found.1] at output
  exact absurd (RegexTheory.boolean_injective output) (by decide)

/-- Row M4: `a?` is nullable and the wildcard accepts a newline. -/
theorem authored_optional_nullable_and_wildcard_newline :
    RegexTheory.Step
        (RegexTheory.nullable (RegexTheory.encode (scalarRegex (optional (literal 'a')))))
        (RegexTheory.boolean true) ∧
      RegexTheory.Step (compiled any "\n") (RegexTheory.boolean true) :=
  ⟨(authored_nullable_iff _ _).mpr optional_nullable_and_wildcard_newline.1,
    optional_nullable_and_wildcard_newline.2 ▸ authored_step_of_fullMatch any "\n"⟩

/-- Row M5: `a{2,3}` on one, three and four letters. -/
theorem authored_range_two_to_three :
    RegexTheory.Step (compiled (boundedRepeat (literal 'a') 2 3) "a")
        (RegexTheory.boolean false) ∧
      RegexTheory.Step (compiled (boundedRepeat (literal 'a') 2 3) "aaa")
        (RegexTheory.boolean true) ∧
      RegexTheory.Step (compiled (boundedRepeat (literal 'a') 2 3) "aaaa")
        (RegexTheory.boolean false) :=
  ⟨range_two_to_three.1 ▸ authored_step_of_fullMatch _ "a",
    range_two_to_three.2.1 ▸ authored_step_of_fullMatch _ "aaa",
    range_two_to_three.2.2 ▸ authored_step_of_fullMatch _ "aaaa"⟩

/-- Row M6: `a{3,2}` rejects every word. -/
theorem authored_reversed_range_rejects (input : String) :
    RegexTheory.Step (compiled (boundedRepeat (literal 'a') 3 2) input)
      (RegexTheory.boolean false) := by
  refine (authored_rejects_iff _ input).mpr fun member => ?_
  rw [language_boundedRepeat_of_reversed (literal 'a') (by decide : 2 < 3)] at member
  exact Language.notMem_zero _ member

/-- Row D1 as the authored rules produce it: the derivative of `a+` by `a` is
the concatenation of the empty word with `a*`. -/
theorem authored_derivative_of_someAs :
    RegexTheory.Step
      (RegexTheory.derivative (RegexTheory.scalar (String.singleton 'a'))
        (RegexTheory.encode (scalarRegex someAs)))
      (RegexTheory.encode (scalarRegex (1 * (literal 'a').star))) :=
  unsimplified_derivative_of_someAs.1 ▸ authored_derivative_runs 'a' someAs

/-- The authored rules do not produce the listed `a*`. -/
theorem authored_derivative_is_unsimplified :
    ¬ RegexTheory.Step
      (RegexTheory.derivative (RegexTheory.scalar (String.singleton 'a'))
        (RegexTheory.encode (scalarRegex someAs)))
      (RegexTheory.encode (scalarRegex (literal 'a').star)) := by
  intro step
  have equal := RegexTheory.encode_injective (authored_derivative_output_eq 'a' someAs _ step)
  revert equal
  decide

end Mettapedia.GSLT.LanguageDef.RegexObservationTable
