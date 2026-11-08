import Mettapedia.Languages.CHR.MachineReady

/-! Bounded runs compose: running `first` ticks and then `second` is running
`first + second`; a stopped or finished state stays put; runs keep the heads
invariant. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

/-- A state the machine still works on. -/
def Active (state : State) : Prop := state.status = .running ∧ state.tasks ≠ []

theorem advance_stopped (table : Table) (state : State) (stopped : ¬ Active state) :
    ∀ budget, advance table budget state = state
  | 0 => rfl
  | budget + 1 => by
    unfold advance
    split
    · rename_i tasks running nonempty
      exfalso
      apply stopped
      refine ⟨by simpa using running, ?_⟩
      rw [nonempty]
      simp
    · rfl

theorem advance_active (table : Table) (state : State) (active : Active state) (budget : Nat) :
    advance table (budget + 1) state = advance table budget (tick table state) := by
  obtain ⟨running, nonempty⟩ := active
  rw [advance.eq_2]
  cases tasks : state.tasks with
  | nil => exact absurd tasks nonempty
  | cons task tail => simp only [running]

theorem advance_add (table : Table) :
    ∀ (first second : Nat) (state : State),
      advance table second (advance table first state) = advance table (first + second) state
  | 0, second, state => by simp [advance]
  | first + 1, second, state => by
    by_cases active : Active state
    · rw [advance_active table state active, advance_add table first second,
        show first + 1 + second = (first + second) + 1 by omega, advance_active table state active]
    · rw [advance_stopped table state active (first + 1), advance_stopped table state active second,
        advance_stopped table state active (first + 1 + second)]

theorem advance_ready (table : Table) (headed : TableHeaded table) :
    ∀ (budget : Nat) (state : State), Ready state → Ready (advance table budget state)
  | 0, _, ready => ready
  | budget + 1, state, ready => by
    by_cases active : Active state
    · rw [advance_active table state active]
      exact advance_ready table headed budget _ (tick_ready table headed state ready)
    · rw [advance_stopped table state active]
      exact ready

#print axioms advance_add
#print axioms advance_ready

end Mettapedia.Languages.CHR.Machine
