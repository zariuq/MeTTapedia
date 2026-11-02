import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalRowReflection

/-! Exact guard availability inside the input-derived envelope. The
statement distinguishes missing evidence outside the envelope from false
comparisons within it; it does not grant imported-module admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation

open Mettapedia.Languages

theorem reached_left_guard_row {input state : Maude.Term} {sort : String}
    (path : Maude.EquationPath Maude.Examples.conditional [] sort input state)
    (left right : Nat)
    (inside : Maude.ConditionalMax.successorCount
      (Maude.ConditionalMax.maximum (Maude.ConditionalMax.numeral left) (Maude.ConditionalMax.numeral right)) ≤
      Maude.ConditionalMax.successorCount state)
    (ordered : right ≤ left) :
    trueRow right left ∈ (provider (Maude.ConditionalMax.successorCount input)).rows := by
  have bounds := numeral_guard_bounded input left right (Nat.le_trans inside (Maude.ConditionalMax.equationPath_count path))
  exact (trueRow_member_iff _ right left).mpr ⟨bounds.2, bounds.1, ordered⟩

theorem reached_right_guard_row {input state : Maude.Term} {sort : String}
    (path : Maude.EquationPath Maude.Examples.conditional [] sort input state)
    (left right : Nat)
    (inside : Maude.ConditionalMax.successorCount
      (Maude.ConditionalMax.maximum (Maude.ConditionalMax.numeral left) (Maude.ConditionalMax.numeral right)) ≤
      Maude.ConditionalMax.successorCount state)
    (ordered : left ≤ right) :
    trueRow left right ∈ (provider (Maude.ConditionalMax.successorCount input)).rows := by
  have bounds := numeral_guard_bounded input left right (Nat.le_trans inside (Maude.ConditionalMax.equationPath_count path))
  exact (trueRow_member_iff _ left right).mpr ⟨bounds.1, bounds.2, ordered⟩

theorem bounded_guard_exact (input : Maude.Term) (left right : Nat)
    (leftBound : left ≤ Maude.ConditionalMax.successorCount input)
    (rightBound : right ≤ Maude.ConditionalMax.successorCount input) :
    trueRow left right ∈ (provider (Maude.ConditionalMax.successorCount input)).rows ↔ left ≤ right := by
  rw [trueRow_member_iff]
  exact ⟨fun facts => facts.2.2, fun ordered => ⟨leftBound, rightBound, ordered⟩⟩

#print axioms bounded_guard_exact
#print axioms reached_left_guard_row
#print axioms reached_right_guard_row

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation
