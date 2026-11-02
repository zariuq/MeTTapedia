import Mettapedia.Languages.OCaml.Machine

/-! A finite completed source run supplies its own next-step witness unless
it has already halted. Invalid source transitions cannot occur on that run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

theorem completed_run_cases {program : Program} {budget : Nat} {source : MachineState} {result : Result}
    (completed : run program budget source = .complete result) :
    source = .halted result ∨ ∃ next work, machineStep program source = .ok (some next) ∧
      run program work next = .complete result := by
  cases source with
  | halted actual =>
    cases budget <;> exact .inl (congrArg MachineState.halted (RunResult.complete.inj completed))
  | evaluate reference captured rest =>
    cases budget with
    | zero => cases completed
    | succ budget =>
      cases stepping : machineStep program (.evaluate reference captured rest) with
      | error error => simp [run, stepping] at completed
      | ok target =>
        cases target with
        | none => simp [run, stepping] at completed
        | some next => exact .inr ⟨next, budget, rfl, by simpa only [run, stepping] using completed⟩
  | returned actual rest =>
    cases budget with
    | zero => cases completed
    | succ budget =>
      cases stepping : machineStep program (.returned actual rest) with
      | error error => simp [run, stepping] at completed
      | ok target =>
        cases target with
        | none => simp [run, stepping] at completed
        | some next => exact .inr ⟨next, budget, rfl, by simpa only [run, stepping] using completed⟩

theorem completed_run_successor {program : Program} {budget : Nat} {source next : MachineState} {result : Result}
    (completed : run program budget source = .complete result)
    (step : machineStep program source = .ok (some next)) :
    ∃ work, run program work next = .complete result := by
  rcases completed_run_cases completed with stopped | ⟨actual, work, actualStep, done⟩
  · subst source
    cases step
  · have same := Option.some.inj (Except.ok.inj (actualStep.symm.trans step))
    subst actual
    exact ⟨work, done⟩

theorem completed_run_successor_smaller {program : Program} {budget : Nat}
    {source next : MachineState} {result : Result}
    (completed : run program budget source = .complete result)
    (step : machineStep program source = .ok (some next)) :
    ∃ work < budget, run program work next = .complete result := by
  cases source with
  | halted actual => cases step
  | evaluate reference captured rest =>
    cases budget with
    | zero => cases completed
    | succ budget =>
      exact ⟨budget, Nat.lt_succ_self _, by simpa only [run, step] using completed⟩
  | returned actual rest =>
    cases budget with
    | zero => cases completed
    | succ budget =>
      exact ⟨budget, Nat.lt_succ_self _, by simpa only [run, step] using completed⟩

#print axioms completed_run_cases
#print axioms completed_run_successor
#print axioms completed_run_successor_smaller

end Mettapedia.Languages.OCaml
