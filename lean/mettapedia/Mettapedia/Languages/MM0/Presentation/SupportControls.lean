import Mettapedia.Languages.MM0.Presentation.SupportCorrespondence
import Mettapedia.Languages.MM0.Kernel.FreeVariables

/-! # Occurrence-support controls, including its distinction from free variables -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalSupport.Controls

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def context : Context := [.bound 0, .regular 1 {0, 2}, .bound 0]

private theorem sorted_dependencies : ({0, 2} : Finset Nat).sort (· ≤ ·) = [0, 2] := by
  rw [Finset.sort_insert (· ≤ ·) (by simp) (by decide)]
  simp

private theorem run_of_computed (source : Preterm) (result : Option (List Nat))
    (computed : indices? context source = result) :
    Applies supportProgram computationalHost "mm0:support" [encodeContext context, encode source]
      (encodeResult result) := by
  simpa only [computed] using support_computes context source

theorem bound_occurrence_computes :
    Applies supportProgram computationalHost "mm0:support" [encodeContext context, encode (.var 2)]
      (encodeResult (some [2])) := run_of_computed _ _ (by decide)

theorem regular_dependencies_computed :
    Applies supportProgram computationalHost "mm0:support" [encodeContext context, encode (.var 1)]
      (encodeResult (some [0, 2])) := run_of_computed _ _ (by simp [indices?, context, sorted_dependencies])

theorem occurrence_order_retained :
    Applies supportProgram computationalHost "mm0:support"
      [encodeContext context, encode (.app (.var 2) (.var 0))]
      (encodeResult (some [2, 0])) := run_of_computed _ _ (by decide)

theorem duplicate_occurrences_retained :
    Applies supportProgram computationalHost "mm0:support"
      [encodeContext context, encode (.app (.var 0) (.var 0))]
      (encodeResult (some [0, 0])) := run_of_computed _ _ (by decide)

theorem dependencies_and_bound_occurrences_both_retained :
    Applies supportProgram computationalHost "mm0:support"
      [encodeContext context, encode (.app (.var 1) (.var 2))]
      (encodeResult (some [0, 2, 2])) := run_of_computed _ _ (by simp [indices?, context, sorted_dependencies])

theorem no_occurrence_is_successful_empty_result :
    Applies supportProgram computationalHost "mm0:support" [encodeContext context, encode (.term 0)]
      (encodeResult (some [])) := run_of_computed _ _ (by decide)

theorem undefined_variable_refuses :
    Applies supportProgram computationalHost "mm0:support" [encodeContext context, encode (.var 3)]
      (encodeResult none) := run_of_computed _ _ (by decide)

theorem undefined_child_refuses_whole_application :
    Applies supportProgram computationalHost "mm0:support"
      [encodeContext context, encode (.app (.var 0) (.var 3))]
      (encodeResult none) := run_of_computed _ _ (by decide)

theorem undefined_function_refuses_whole_application :
    Applies supportProgram computationalHost "mm0:support"
      [encodeContext context, encode (.app (.var 3) (.var 0))]
      (encodeResult none) := run_of_computed _ _ (by decide)

theorem missing_dependency_cannot_be_returned :
    ¬ Applies supportProgram computationalHost "mm0:support" [encodeContext context, encode (.var 1)]
      (encodeResult (some [0])) := by
  intro wrong
  have same := encodeResult_injective (wrong.deterministic regular_dependencies_computed)
  cases same

theorem refused_variable_cannot_be_an_empty_support :
    ¬ Applies supportProgram computationalHost "mm0:support" [encodeContext context, encode (.var 3)]
      (encodeResult (some [])) := by
  intro wrong
  have same := encodeResult_injective (wrong.deterministic undefined_variable_refuses)
  cases same

theorem zero_fuel_does_not_mean_empty_or_refused :
    apply supportProgram computationalHost 0 "mm0:support"
      [encodeContext context, encode (.term 0)] = .exhausted := rfl

private def bindingSignature : TermSignature
  | 0 => some ⟨[.bound 0, .regular 1 {0}], 1, {}⟩
  | _ => none

private def bindingTerm : Preterm := .applyArgs (.term 0) [.var 0, .var 1]

theorem binding_does_not_erase_occurrence_support :
    Applies supportProgram computationalHost "mm0:support" [encodeContext context, encode bindingTerm]
      (encodeResult (some [0, 0, 2])) := run_of_computed _ _
        (by simp [indices?, context, bindingTerm, Preterm.applyArgs, sorted_dependencies])

theorem binding_does_erase_its_image_from_free_variables :
    Preterm.freeVariables? bindingSignature context bindingTerm = some {2} := by decide

theorem support_and_free_variables_are_different :
    Preterm.support? context bindingTerm ≠ Preterm.freeVariables? bindingSignature context bindingTerm := by
  decide

end Mettapedia.Languages.MM0.Presentation.ComputationalSupport.Controls
