import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCaseProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklistControls

/-!
# Executed binding recovery exposes the body used by progress

Swapped parameters recover the second formal position. Reversing the
equation selects that same declaration. Repetition, compound arguments and
unavailable ambient variables retain their negative binding-case outcomes.
An independently supplied model survives the computed case with strictly
smaller active support potential.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCaseControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualBindingCase
open ContextualActiveSupport

abbrev base := ContextualBindingWorklist.Controls.base
abbrev declaration := ContextualBindingWorklist.Controls.declaration
abbrev extended := signature base declaration
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)

def first : Term extended [(), ()] () :=
  ContextualBindingWorklist.Controls.call (.var (.succ .zero)) (.var .zero)
def second : Term extended [(), ()] () := .var .zero
def remaining : Problem declaration :=
  [(observe (ContextualBindingWorklist.Controls.closed (Γ := [])),
    observe (ContextualBindingWorklist.Controls.constant (Γ := [])))]
def problem : Problem declaration := (observe first, observe second) :: remaining

def chosen? {Γ : Ctx base} {sort : base.Srt} {left right : Term extended Γ sort}
    (binding : Option (Case left right)) : Option Bool := binding.map Case.chosen

def position? {Γ : Ctx base} {sort : base.Srt} {left right : Term extended Γ sort}
    (binding : Option (Case left right)) : Option Nat := binding.bind fun found =>
  match found.body with
  | .var position => some (CommonABT.index (S := extended) position)
  | .op _ _ => none

theorem swapped_recovery_selects_the_actual_open_declaration :
    chosen? (tryTerms first second) = some false := by
  decide +kernel

theorem its_body_is_the_second_formal_parameter : position? (tryTerms first second) = some 1 := by
  decide +kernel

theorem the_reverse_orientation_recovers_the_same_body : position? (tryTerms second first) = some 1 := by
  decide +kernel

def repeated : Term extended [()] () := ContextualBindingWorklist.Controls.call (.var .zero) (.var .zero)
def repeatedTarget : Term extended [()] () := .var .zero
theorem repetition_does_not_create_a_unique_recovery_case :
    (tryTerms repeated repeatedTarget).isSome = false := by
  decide +kernel

def compound : Term extended [] () :=
  ContextualBindingWorklist.Controls.call ContextualBindingWorklist.Controls.constant
    ContextualBindingWorklist.Controls.constant
theorem compound_arguments_remain_outside_unique_recovery :
    (tryTerms compound (ContextualBindingWorklist.Controls.constant (Γ := []))).isSome = false := by
  decide +kernel

def capture : Term extended [(), (), ()] () :=
  ContextualBindingWorklist.Controls.call (.var (.succ .zero)) (.var (.succ (.succ .zero)))
def outside : Term extended [(), (), ()] () := .var .zero
theorem the_body_cannot_capture_the_missing_ambient_variable : (tryTerms capture outside).isSome = false := by
  decide +kernel

def candidate : Assignment declaration declaration
  | false => .var (.succ .zero)
  | true => ContextualBindingWorklist.Controls.constant

theorem the_original_problem_has_an_independent_model : Models candidate problem := by
  intro equation member
  simp only [problem, remaining, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem the_case_actually_returned_by_recovery_preserves_that_model_and_decreases_work :
    ∃ found, tryTerms first second = some found ∧
      Models candidate (mapProblem (ContextualBindingCaseProgress.answer found) remaining) ∧
      (∀ identity, candidate identity =
        instantiate candidate (ContextualBindingCaseProgress.answer found identity)) ∧
      potential candidate (active (mapProblem (ContextualBindingCaseProgress.answer found) remaining)) <
        potential candidate (active problem) := by
  have present : (tryTerms first second).isSome = true := by decide +kernel
  cases computed : tryTerms first second with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at present
  | some found =>
      exact ⟨found, rfl, ContextualBindingCaseProgress.model_progress found remaining candidate
        the_original_problem_has_an_independent_model⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCaseControls
