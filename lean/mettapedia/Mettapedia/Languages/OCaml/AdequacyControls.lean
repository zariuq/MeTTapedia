import Mettapedia.Languages.OCaml.ObservationAdequacy
import Mettapedia.Languages.OCaml.EvaluationControls

/-! Positive and all-budget negative consequences of the reference-machine
adequacy theorem, instantiated at the standard core programs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.AdequacyControls

open Examples EvaluationControls

theorem recursion_eventually_checked : ∃ budget,
    (checkedObservation recursion budget (.ok (.tuple [integer 720, integer 55]))).isSome = true :=
  evaluates_iff_checked.mp recursion_evaluates

theorem wrong_recursion_result_refused (budget : Nat) :
    observes recursion budget (.ok (.tuple [integer 720, integer 54])) = false := by
  apply wrong_observation_refused recursion_evaluates
  intro impossible
  have same := congrArg (fun result => resultEqual result (.ok (.tuple [integer 720, integer 55]))) impossible
  have left : resultEqual (.ok (.tuple [integer 720, integer 54])) (.ok (.tuple [integer 720, integer 55])) = false := by cbv
  have right : resultEqual (.ok (.tuple [integer 720, integer 55])) (.ok (.tuple [integer 720, integer 55])) = true :=
    (resultEqual_iff _ _).mpr rfl
  rw [left, right] at same
  cases same

theorem mismatch_never_value (value : Value) (budget : Nat) : observes matchFailure budget (.ok value) = false :=
  source_fault_never_value mismatch_is_fault value budget

theorem evaluation_order_fault_never_value (value : Value) (budget : Nat) :
    observes rightToLeftFault budget (.ok value) = false :=
  source_fault_never_value right_to_left_fault value budget

theorem closure_result_never_fault (fault : Fault) (budget : Nat) : observes closures budget (.error fault) = false :=
  source_value_never_fault closures_evaluates fault budget

theorem recursive_result_unique {result : Result} (evaluated : Evaluates recursion [] recursion.entry result) :
    result = .ok (.tuple [integer 720, integer 55]) :=
  evaluates_deterministic evaluated recursion_evaluates

#print axioms wrong_recursion_result_refused
#print axioms mismatch_never_value
#print axioms recursive_result_unique

end Mettapedia.Languages.OCaml.AdequacyControls
