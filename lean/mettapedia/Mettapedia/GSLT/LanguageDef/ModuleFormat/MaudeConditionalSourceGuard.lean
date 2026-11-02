import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalGuardCertificate
import Mettapedia.Languages.Maude.ConditionalMaxInterpretation

/-! Two-sided source meaning for the finite guard snapshot. The bounded
provider realizes exactly the source's true numeral comparisons inside
the input envelope; lack of a row outside that envelope is not falsity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation

open Mettapedia.Languages
open Maude.ConditionalMax

theorem bounded_source_guard_iff (bound left right : Nat)
    (leftBound : left ≤ bound) (rightBound : right ≤ bound) :
    trueRow left right ∈ (provider bound).rows ↔
      Maude.Equivalent Maude.Examples.conditional [] "Bool" (le (numeral left) (numeral right)) truth := by
  rw [trueRow_member_iff, comparison_true_iff]
  exact ⟨fun facts => facts.2.2, fun ordered => ⟨leftBound, rightBound, ordered⟩⟩

theorem reached_left_source_guard_iff {input state : Maude.Term} {sort : String}
    (path : Maude.EquationPath Maude.Examples.conditional [] sort input state)
    (left right : Nat)
    (inside : successorCount (maximum (numeral left) (numeral right)) ≤ successorCount state) :
    trueRow right left ∈ (provider (successorCount input)).rows ↔
      Maude.Equivalent Maude.Examples.conditional [] "Bool" (le (numeral right) (numeral left)) truth := by
  have bounds := numeral_guard_bounded input left right (Nat.le_trans inside (equationPath_count path))
  exact bounded_source_guard_iff _ right left bounds.2 bounds.1

theorem reached_right_source_guard_iff {input state : Maude.Term} {sort : String}
    (path : Maude.EquationPath Maude.Examples.conditional [] sort input state)
    (left right : Nat)
    (inside : successorCount (maximum (numeral left) (numeral right)) ≤ successorCount state) :
    trueRow left right ∈ (provider (successorCount input)).rows ↔
      Maude.Equivalent Maude.Examples.conditional [] "Bool" (le (numeral left) (numeral right)) truth := by
  have bounds := numeral_guard_bounded input left right (Nat.le_trans inside (equationPath_count path))
  exact bounded_source_guard_iff _ left right bounds.1 bounds.2

example : trueRow 2 3 ∈ (provider 3).rows :=
  (bounded_source_guard_iff 3 2 3 (by omega) (by omega)).mpr
    ((comparison_true_iff 2 3).mpr (by omega))

example : trueRow 3 2 ∉ (provider 3).rows := by
  rw [bounded_source_guard_iff 3 3 2 (by omega) (by omega)]
  exact false_comparison_not_true 3 2 (by omega)

example : trueRow 0 1 ∉ (provider 0).rows := by
  rw [trueRow_member_iff]
  omega

example : Maude.Equivalent Maude.Examples.conditional [] "Bool" (le (numeral 0) (numeral 1)) truth :=
  (comparison_true_iff 0 1).mpr (by omega)

#print axioms bounded_source_guard_iff
#print axioms reached_left_source_guard_iff
#print axioms reached_right_source_guard_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation
