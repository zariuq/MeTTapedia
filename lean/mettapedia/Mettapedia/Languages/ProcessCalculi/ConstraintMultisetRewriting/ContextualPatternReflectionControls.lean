import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPatternImages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragmentControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCaseControls

/-!
# Renaming reflection and actual recovered pattern images

Mixed-sort permutations and a field's own binder remain available. No
renaming can turn repeated or compound arguments into the distinct-variable
fragment. The actual selected swapped binding preserves its retained queue,
while the missing ambient variable still prevents recovery.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternReflectionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment

namespace Mixed

open ContextualPatternFragment.Controls
abbrev base := ContextualFrameSelection.Controls.base

def exchange : Ren base [false, true] [true, false]
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ impossible) => nomatch impossible

theorem a_mixed_sort_permutation_reflects_its_pattern : Pattern base declaration swapped := by
  apply rename_reflects (S := base) (source := declaration) swapped exchange
  apply check_sound
  decide +kernel

theorem no_renaming_can_repair_repeated_arguments {Γ : Ctx base} (rho : Ren base [false] Γ) :
    ¬ Pattern base declaration (rename (S := extended) rho repeated) := by
  intro patterned
  have original := rename_reflects (S := base) (source := declaration) repeated rho patterned
  have checked := check_complete repeated original
  rw [repeated_arguments_are_outside_the_distinct_fragment] at checked
  cases checked

theorem no_renaming_can_repair_compound_arguments {Γ : Ctx base} (rho : Ren base [] Γ) :
    ¬ Pattern base declaration (rename (S := extended) rho compound) := by
  intro patterned
  have original := rename_reflects (S := base) (source := declaration) compound rho patterned
  have checked := check_complete compound original
  rw [compound_arguments_are_outside_the_distinct_fragment] at checked
  cases checked

def intoAmbient : Ren base [] [true, false] := fun _ position => nomatch position

theorem widening_the_ambient_context_keeps_the_fields_own_binder :
    Pattern base declaration underBinder := by
  apply rename_reflects (S := base) (source := declaration) underBinder intoAmbient
  apply check_sound
  decide +kernel

theorem reflection_does_not_license_noninjective_preservation :
    check (rename (S := extended) ContextualFrameSelection.Controls.repeatedMap
      (generator declaration 1)) = false := by
  decide +kernel

end Mixed

namespace Recovery

open ContextualBindingPatternImages
abbrev base := ContextualBindingCaseControls.base
abbrev source := ContextualBindingCaseControls.declaration
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

theorem the_original_swapped_queue_is_in_the_fragment : ProblemPattern ContextualBindingCaseControls.problem := by
  intro equation member
  simp only [ContextualBindingCaseControls.problem, ContextualBindingCaseControls.remaining,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals constructor <;> apply check_sound <;> decide +kernel

theorem the_executed_choice_has_pattern_images_and_a_pattern_residual :
    ∃ selection, ContextualBindingWorklist.select ContextualBindingCaseControls.problem = some selection ∧
      (∀ identity, Pattern base source (selection.update.answer identity)) ∧
      ProblemPattern selection.update.remaining := by
  have present : (ContextualBindingWorklist.select ContextualBindingCaseControls.problem).isSome = true := by
    decide +kernel
  cases computed : ContextualBindingWorklist.select ContextualBindingCaseControls.problem with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at present
  | some selection =>
      exact ⟨selection, rfl, selected_images selection the_original_swapped_queue_is_in_the_fragment,
        selection_preserves selection the_original_swapped_queue_is_in_the_fragment⟩

theorem the_missing_ambient_variable_still_prevents_recovery :
    (ContextualBindingCase.tryTerms ContextualBindingCaseControls.capture ContextualBindingCaseControls.outside).isSome = false := by
  decide +kernel

end Recovery

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternReflectionControls
