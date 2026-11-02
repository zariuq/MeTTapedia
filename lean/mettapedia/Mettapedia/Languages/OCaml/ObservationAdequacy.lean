import Mettapedia.Languages.OCaml.MachineCompleteness
import Mettapedia.Languages.OCaml.ObservationChecking

/-! The proof-producing observation checker is adequate for the independent
evaluation judgments once given a sufficient budget. A smaller budget may
remain pending; no budget can accept a different value or fault.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

theorem evaluates_iff_observed {program : Program} {result : Result} :
    Evaluates program [] program.entry result ↔ ∃ budget, observes program budget result = true := by
  rw [evaluates_iff_completed_run]
  exact ⟨fun ⟨budget, completed⟩ => ⟨budget, (observes_iff _ _ _).mpr completed⟩,
    fun ⟨budget, accepted⟩ => ⟨budget, (observes_iff _ _ _).mp accepted⟩⟩

theorem evaluates_iff_checked {program : Program} {result : Result} :
    Evaluates program [] program.entry result ↔
      ∃ budget, (checkedObservation program budget result).isSome = true := by
  rw [evaluates_iff_completed_run]
  exact ⟨fun ⟨budget, completed⟩ => ⟨budget, (checkedObservation_iff _ _ _).mpr completed⟩,
    fun ⟨budget, accepted⟩ => ⟨budget, (checkedObservation_iff _ _ _).mp accepted⟩⟩

theorem observes_stable {program : Program} {budget extra : Nat} {result : Result}
    (accepted : observes program budget result = true) : observes program (budget + extra) result = true :=
  (observes_iff _ _ _).mpr (run_complete_stable ((observes_iff _ _ _).mp accepted))

theorem wrong_observation_refused {program : Program} {correct wrong : Result}
    (evaluated : Evaluates program [] program.entry correct) (different : wrong ≠ correct) (budget : Nat) :
    observes program budget wrong = false := by
  cases checked : observes program budget wrong with
  | false => rfl
  | true => exact (different (evaluates_deterministic (observes_sound checked) evaluated)).elim

theorem source_fault_never_value {program : Program} {fault : Fault}
    (evaluated : Evaluates program [] program.entry (.error fault)) (value : Value) (budget : Nat) :
    observes program budget (.ok value) = false :=
  wrong_observation_refused evaluated (by intro impossible; cases impossible) budget

theorem source_value_never_fault {program : Program} {value : Value}
    (evaluated : Evaluates program [] program.entry (.ok value)) (fault : Fault) (budget : Nat) :
    observes program budget (.error fault) = false :=
  wrong_observation_refused evaluated (by intro impossible; cases impossible) budget

#print axioms evaluates_iff_checked
#print axioms observes_stable
#print axioms wrong_observation_refused

end Mettapedia.Languages.OCaml
