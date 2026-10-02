import Mettapedia.GSLT.LanguageDef.RegexAuthoredComparison
import Mettapedia.GSLT.LanguageDef.RegexTheoryValidation
import Mettapedia.Computability.RegularLanguages.AlphabetMap

/-!
# Unicode-scalar interpretation of authored regex requests

Character expressions and input strings compile to the authored constructor
presentation using one singleton string per Unicode scalar. The admission and
semantic comparison are qualified to this input image. The underlying raw
String alphabet also permits letters containing several scalars; it is not
identified with the Char alphabet or with UTF-8 bytes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexCharacterInterpretation

open Mettapedia.Computability.RegularLanguages
open Mettapedia.OSLF.MeTTaIL.Syntax
open RegexAuthoredComparison
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted (checkHasType)

/-- Compile a character request through the singleton-string alphabet embedding. -/
def request (p : Regex Char) (input : String) : Request :=
  .matchWord (scalarRegex p) (scalarInput input)

def compiled (p : Regex Char) (input : String) : Pattern := encodeRequest (request p input)

/-- Every compiled scalar request is admitted by the authored carrier checker. -/
theorem compiled_admitted (p : Regex Char) (input : String)
    (free : FreeTypeContext) (bound : List TypeExpr) :
    checkHasType RegexTheory.theory free bound (compiled p input) (.base "Bool") = true :=
  RegexTheory.check_matchRequest (scalarRegex p) (scalarInput input) free bound

theorem evidence_accepts_iff (p : Regex Char) (input : String) :
    Nonempty (Evidence (request p input) true) ↔ input.toList ∈ language p := by
  change Nonempty (RegexDerivatives.Match (scalarRegex p) (scalarInput input) true) ↔ _
  rw [RegexDerivatives.Match.accepts_iff]
  exact mapped_word_mem_language String.singleton stringSingleton_injective p input.toList

theorem evidence_rejects_iff (p : Regex Char) (input : String) :
    Nonempty (Evidence (request p input) false) ↔ input.toList ∉ language p := by
  change Nonempty (RegexDerivatives.Match (scalarRegex p) (scalarInput input) false) ↔ _
  rw [RegexDerivatives.Match.rejects_iff]
  exact not_congr (mapped_word_mem_language String.singleton stringSingleton_injective p input.toList)


/-- Authored execution and independent character-language membership coincide. -/
theorem authored_accepts_iff (p : Regex Char) (input : String) :
    RegexTheory.Step (compiled p input) (RegexTheory.boolean true) ↔
      input.toList ∈ language p :=
  (step_iff_evidence (request p input) true).trans (evidence_accepts_iff p input)

/-- Rejection is reflected as well as acceptance; no additional raw output is assumed away. -/
theorem authored_rejects_iff (p : Regex Char) (input : String) :
    RegexTheory.Step (compiled p input) (RegexTheory.boolean false) ↔
      input.toList ∉ language p :=
  (step_iff_evidence (request p input) false).trans (evidence_rejects_iff p input)

/-- Every actual raw output is exactly the encoded character matcher result. -/
theorem authored_output_eq (p : Regex Char) (input : String) (output : Pattern)
    (step : RegexTheory.Step (compiled p input) output) :
    output = RegexTheory.boolean (fullMatch p input.toList) := by
  have correct := step_output_eq (request := request p input) step
  change output = RegexTheory.boolean (fullMatch (scalarRegex p) (scalarInput input)) at correct
  simpa only [fullMatch_scalarRegex] using correct


/-- Nullability is independent of the character alphabet spelling. -/
theorem authored_nullable_iff (p : Regex Char) (result : Bool) :
    RegexTheory.Step (RegexTheory.nullable (RegexTheory.encode (scalarRegex p)))
      (RegexTheory.boolean result) ↔ p.matchEpsilon = result := by
  rw [nullable_steps_iff]
  exact (congrArg (· = result) (mapAlphabet_nullable String.singleton p)).to_iff

/-- Every character derivative is produced by the authored recursive rule actions. -/
theorem authored_derivative_runs (a : Char) (p : Regex Char) :
    RegexTheory.Step
      (RegexTheory.derivative (RegexTheory.scalar (String.singleton a)) (RegexTheory.encode (scalarRegex p)))
      (RegexTheory.encode (scalarRegex (derivative a p))) := by
  apply (derivative_steps_iff _ _ _).mpr
  exact derivative_mapAlphabet String.singleton stringSingleton_injective a p

/-- The derivative correspondence reflects every raw output, with no prior decoder assumption. -/
theorem authored_derivative_output_eq (a : Char) (p : Regex Char) (output : Pattern)
    (step : RegexTheory.Step
      (RegexTheory.derivative (RegexTheory.scalar (String.singleton a)) (RegexTheory.encode (scalarRegex p)))
      output) : output = RegexTheory.encode (scalarRegex (derivative a p)) := by
  have correct := step_output_eq (request := .derivative (String.singleton a) (scalarRegex p)) step
  change output = RegexTheory.encode (derivative (String.singleton a) (scalarRegex p)) at correct
  rw [show derivative (String.singleton a) (scalarRegex p) = scalarRegex (derivative a p) from
    derivative_mapAlphabet String.singleton stringSingleton_injective a p] at correct
  exact correct

namespace Controls

theorem unicode_literal_runs :
    RegexTheory.Step (compiled (literal 'é') "é") (RegexTheory.boolean true) := by
  apply (authored_accepts_iff _ _).mpr
  exact (fullMatch_correct _ _).mp (by decide)

theorem different_letter_cannot_accept :
    ¬ RegexTheory.Step (compiled (literal 'é') "e") (RegexTheory.boolean true) := by
  rw [authored_accepts_iff, ← fullMatch_correct]
  decide

theorem wildcard_consumes_scalar :
    RegexTheory.Step (compiled any "🦀") (RegexTheory.boolean true) := by
  apply (authored_accepts_iff _ _).mpr
  exact (fullMatch_correct _ _).mp (by decide)

theorem wildcard_does_not_consume_two_scalars :
    RegexTheory.Step (compiled any "🦀é") (RegexTheory.boolean false) := by
  rw [authored_rejects_iff, ← fullMatch_correct]
  decide

theorem wildcard_includes_newline :
    RegexTheory.Step (compiled any "\n") (RegexTheory.boolean true) := by
  apply (authored_accepts_iff _ _).mpr
  exact (fullMatch_correct _ _).mp (by decide)

end Controls

end Mettapedia.GSLT.LanguageDef.RegexCharacterInterpretation
