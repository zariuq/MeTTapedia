import Mettapedia.Languages.OCaml.ObservationChecking
import Mettapedia.Languages.OCaml.Examples

/-! Observation admission checks complete results, including faults, while
refusing a wrong result, a pending computation and malformed indexed code.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

namespace Mettapedia.Languages.OCaml.ObservationControls

open Examples

theorem standard_observations_checked : examples.all (fun sample =>
    (checkedObservation sample.program 20000 sample.expected).isSome) = true := by
  rw [List.all_eq_true]
  intro sample member
  apply (checkedObservation_iff sample.program 20000 sample.expected).mpr
  simp only [examples, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cbv

example : observes matchFailure 20000 (.error .matchFailure) = true := by cbv
example : observes matchFailure 20000 (.ok (integer 0)) = false := by cbv
example : observes rightToLeftFault 20000 (.error .divisionByZero) = true := by cbv
example : observes rightToLeftFault 20000 (.error .matchFailure) = false := by cbv
example : observes looping 2000 (.ok (integer 0)) = false := by cbv
example : observes priority 0 (.ok (integer 2)) = false := by cbv
example : observes ({code := #[], entry := 0} : Program) 10 (.ok (integer 0)) = false := by cbv

example : resultEqual (.ok (.closure (.lambda 2) [integer 3]))
    (.ok (.closure (.lambda 2) [integer 4])) = false := by cbv
example : resultEqual (.ok (.variant 0 1 [integer 3]))
    (.ok (.variant 0 2 [integer 3])) = false := by cbv

#print axioms standard_observations_checked

end Mettapedia.Languages.OCaml.ObservationControls
