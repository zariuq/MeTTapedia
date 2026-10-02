import Mettapedia.GSLT.LanguageDef.RegexAuthoredComparison

/-!
# Discriminating authored regex controls

These examples use the actual contextual rule interpreter. Unicode strings
remain scalar data, and insufficient derivation depth returns no observation
rather than a false rejection. Nullable concatenation and wildcard matching
exercise recursive rules beyond literal equality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexAuthoredControls

open Mettapedia.Computability.RegularLanguages
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open RegexAuthoredComparison

/-- A positive literal request requires its derivative and final nullable rule. -/
theorem literal_depth_three :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory 3
      (encodeRequest (.matchWord (literal "λ") ["λ"])) = [RegexTheory.boolean true] := by
  rw [rewriteAt_exact]
  rfl

/-- A mismatching literal produces an actual false observation. -/
theorem literal_mismatch_depth_three :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory 3
      (encodeRequest (.matchWord (literal "λ") ["β"])) = [RegexTheory.boolean false] := by
  rw [rewriteAt_exact]
  rfl

/-- Insufficient depth is not confused with a semantic rejection. -/
theorem insufficient_depth_no_observation :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory 2
      (encodeRequest (.matchWord (literal "λ") ["λ"])) = [] := by
  rw [rewriteAt_exact]
  rfl

/-- Nullable left operands require the concatenation rule's second derivative branch. -/
theorem nullable_left_accepts :
    RegexTheory.Step
      (encodeRequest (.matchWord ((1 + literal "λ") * literal "β") ["β"]))
      (RegexTheory.boolean true) := by
  apply (match_steps_iff _ _ _).mpr
  decide

/-- Consuming the optional left letter does not supply the required right letter. -/
theorem nullable_left_rejects_short_word :
    RegexTheory.Step
      (encodeRequest (.matchWord ((1 + literal "λ") * literal "β") ["λ"]))
      (RegexTheory.boolean false) := by
  apply (match_steps_iff _ _ _).mpr
  decide

theorem literal_cannot_invent_acceptance :
    ¬ RegexTheory.Step (encodeRequest (.matchWord (literal "λ") ["β"]))
      (RegexTheory.boolean true) := by
  intro event
  have impossible : fullMatch (literal "λ") ["β"] ≠ true := by decide
  exact impossible ((match_steps_iff _ _ _).mp event)

/-- Wildcard consumes a scalar newline, without an implicit dot-all flag. -/
theorem wildcard_accepts_newline :
    RegexTheory.Step (encodeRequest (.matchWord any ["\n"])) (RegexTheory.boolean true) := by
  apply (match_steps_iff _ _ _).mpr
  decide

/-- Wildcard consumes one scalar, not an empty word. -/
theorem wildcard_rejects_empty :
    RegexTheory.Step (encodeRequest (.matchWord any [])) (RegexTheory.boolean false) := by
  apply (match_steps_iff _ _ _).mpr
  decide

/-- A scalar equal to a constructor's spelling remains data inside a literal. -/
theorem reserved_spelling_is_scalar :
    RegexTheory.Step (encodeRequest (.matchWord (literal "rx:true") ["rx:true"]))
      (RegexTheory.boolean true) := by
  apply (match_steps_iff _ _ _).mpr
  decide

end Mettapedia.GSLT.LanguageDef.RegexAuthoredControls
