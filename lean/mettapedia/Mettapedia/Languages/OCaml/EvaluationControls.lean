import Mettapedia.Languages.OCaml.MachineCorrectness
import Mettapedia.Languages.OCaml.Examples

/-! The standard programs have independent evaluation derivations, obtained
through the proved machine-soundness theorem and kernel-checked runs.
Fault and pending controls keep those observations distinct from values.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

namespace Mettapedia.Languages.OCaml.EvaluationControls

open Examples

theorem recursion_evaluates :
    Evaluates recursion [] recursion.entry (.ok (.tuple [integer 720, integer 55])) :=
  run_sound (budget := 20000) (by cbv)

theorem lists_evaluates :
    Evaluates lists [] lists.entry
      (.ok (.tuple [list [2, 3, 4], integer 6, list [1, 2, 3, 4], list [3, 2, 1]])) :=
  run_sound (budget := 20000) (by cbv)

theorem mutual_evaluates :
    Evaluates mutualRecursion [] mutualRecursion.entry
      (.ok (.tuple [boolean true, boolean true, boolean false])) :=
  run_sound (budget := 20000) (by cbv)

theorem variants_evaluates :
    Evaluates variants [] variants.entry (.ok (.tuple [integer 42, integer 9])) :=
  run_sound (budget := 20000) (by cbv)

theorem closures_evaluates :
    Evaluates closures [] closures.entry (.ok (.tuple [integer 7, integer 7, integer 13])) :=
  run_sound (budget := 20000) (by cbv)

theorem sorting_evaluates : Evaluates sorting [] sorting.entry (.ok (list [1, 1, 2, 3])) :=
  run_sound (budget := 20000) (by cbv)

theorem priority_evaluates : Evaluates priority [] priority.entry (.ok (integer 2)) :=
  run_sound (budget := 20000) (by cbv)

theorem mismatch_is_fault : Evaluates matchFailure [] matchFailure.entry (.error .matchFailure) :=
  run_sound (budget := 20000) (by cbv)

theorem right_to_left_fault :
    Evaluates rightToLeftFault [] rightToLeftFault.entry (.error .divisionByZero) :=
  run_sound (budget := 20000) (by cbv)

theorem short_circuit_evaluates :
    Evaluates shortCircuit [] shortCircuit.entry (.ok (.tuple [boolean false, boolean true])) :=
  run_sound (budget := 20000) (by cbv)

example : run matchFailure 20000 (begin matchFailure) ≠ .complete (.ok (integer 0)) := by
  cbv
  intro impossible
  cases impossible
example : run rightToLeftFault 20000 (begin rightToLeftFault) ≠ .complete (.ok (integer 0)) := by
  cbv
  intro impossible
  cases impossible
example : ∃ state, run looping 2000 (begin looping) = .pending state := by
  generalize observed : run looping 2000 (begin looping) = result
  cases result with
  | complete value =>
    have pending : (match run looping 2000 (begin looping) with | .pending _ => true | _ => false) = true := by cbv
    rw [observed] at pending
    cases pending
  | invalid error =>
    have pending : (match run looping 2000 (begin looping) with | .pending _ => true | _ => false) = true := by cbv
    rw [observed] at pending
    cases pending
  | pending state => exact ⟨state, rfl⟩

#print axioms recursion_evaluates
#print axioms lists_evaluates
#print axioms right_to_left_fault

end Mettapedia.Languages.OCaml.EvaluationControls
