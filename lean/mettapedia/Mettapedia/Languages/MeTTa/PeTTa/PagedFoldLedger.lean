import Mettapedia.Languages.MeTTa.PeTTa.PagedFold

/-! Every executed driver transition contributes exactly one source or host
debit. Source and host units remain distinct from physical native events. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.PagedFold

open Mettapedia.Machines SpaceSemantics

theorem step_total (program : Program) (callback : FoldSource.Callback) (before after : State)
    (advanced : step program callback before = some after) : after.total = before.total + 1 := by
  cases before with
  | mk phase prefixes sourceDebit hostDebit =>
      cases phase with
      | done | boundary => simp [step] at advanced
      | ready world items accumulator =>
          cases items <;> simp only [step] at advanced
          all_goals cases advanced; simp only [State.total]; omega
      | running call =>
          simp only [step] at advanced
          split at advanced
          all_goals first
            | (cases advanced; simp only [State.total]; omega)
            | (split at advanced <;> cases advanced <;> simp only [State.total] <;> omega)

theorem run_total (program : Program) (callback : FoldSource.Callback) (fuel : Nat) (state : State) :
    (run program callback fuel state).1.total = state.total + (run program callback fuel state).2 := by
  induction fuel generalizing state with
  | zero => simp [run, MachineCore.runSlice]
  | succ fuel ih =>
      cases advanced : step program callback state with
      | none => simp [run, MachineCore.runSlice, core, advanced]
      | some next =>
          have cost := step_total program callback state next advanced
          have tail := ih next
          simp only [run, MachineCore.runSlice, core, advanced]
          dsimp only [run, core] at tail
          rw [tail]
          omega

theorem source_debit_is_not_whole_driver_debit (sourceTicks items : Nat) :
    sourceTicks < sourceTicks + 2 * items + 1 := by omega

end Mettapedia.Languages.MeTTa.PeTTa.PagedFold
