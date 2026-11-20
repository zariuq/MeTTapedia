import Mettapedia.Machines.TIsa.P1WordScalar

/-! # Register frames for structured p1 execution

The syntax-derived write set applies to capability accesses, funding,
early return, and loop control as well as to scalar instructions. In
particular, a loop body with a locked index and bound preserves them
regardless of the chosen branch or the body's outcome.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1WordFrame

open P1Source P1WordExecution
open P1WordScalar (writes)

private theorem write_keeps (before after : State) (register destination : Reg) (value : Word)
    (apart : register ≠ destination)
    (got : (Except.ok (before.write destination value) : Except ExitStatus State) = .ok after) :
    after.registers register = before.registers register := by
  rw [← Except.ok.inj got]
  exact Function.update_of_ne apart ..

private theorem scalar_keeps (code : Instr) (before after : State) (register : Reg)
    (outside : register ∉ writes (.instruction code)) (ran : scalarInstruction before code = .ok after) :
    after.registers register = before.registers register := by
  cases tagged : code.destination? with
  | none =>
    simp only [scalarInstruction, tagged] at ran
    cases ran
  | some destination =>
    have distinct : register ≠ destination := by simpa [writes, tagged] using outside
    simp only [scalarInstruction, tagged] at ran
    split at ran
    · exact write_keeps _ _ _ _ _ distinct ran
    · cases ran

theorem instruction_keeps (code : Instr) (before after : State) (register : Reg)
    (outside : register ∉ writes (.instruction code)) (ran : instruction before code = .ok after) :
    after.registers register = before.registers register := by
  have update (destination : Reg) (value : Word) (identified : code.destination? = some destination)
      (got : Except.ok (before.write destination value) = (Except.ok after : Except ExitStatus State)) :
      after.registers register = before.registers register :=
    write_keeps _ _ _ _ _ (by simpa [writes, identified] using outside) got
  cases code with
  | loadFrame ty dst slot =>
    simp only [instruction] at ran
    split at ran
    · exact update _ _ rfl ran
    · cases ran
  | address region dst base index scale displacement =>
    simp only [instruction] at ran
    split at ran
    · cases ran
    · split at ran
      · exact update _ _ rfl ran
      · cases ran
  | load ty width region dst pointer offset =>
    cases width
    · cases ran
    · cases ran
    · simp only [instruction] at ran
      split at ran
      · cases ran
      · split at ran
        · split at ran
          · exact update _ _ rfl ran
          · cases ran
        · cases ran
  | store width region pointer offset source =>
    cases width
    · cases ran
    · cases ran
    · simp only [instruction] at ran
      split at ran
      · cases ran
      · split at ran
        · rw [← Except.ok.inj ran]
          rfl
        · cases ran
  | _ => exact scalar_keeps _ _ _ _ outside ran

private theorem then_keeps (register : Reg) (before : State) (first : Flow) (next : State → Flow)
    (kept : first.after.registers register = before.registers register)
    (later : ∀ middle, (next middle).after.registers register = middle.registers register) :
    (first.thenContinue next).after.registers register = before.registers register := by
  cases first with
  | continuing middle => exact (later middle).trans kept
  | returned _ _ _ => exact kept

private theorem guard_keeps (register : Reg) (before : State) (guard : Option Reg) (next : State → Flow)
    (kept : ∀ state, (next state).after.registers register = state.registers register) :
    (continueLoop before guard next).after.registers register = before.registers register := by
  cases guard with
  | none => exact kept before
  | some condition =>
    simp only [continueLoop]
    split
    · exact kept before
    · split <;> rfl

theorem loop_keeps (body : State → Flow) (index register : Reg) (guard : Option Reg)
    (apart : register ≠ index) (bodyKeeps : ∀ state, (body state).after.registers register = state.registers register)
    (count : Nat) (state : State) :
    (loop body index guard count state).after.registers register = state.registers register := by
  induction count generalizing state with
  | zero => rfl
  | succ count rest =>
    simp only [loop]
    apply guard_keeps
    intro entered
    apply then_keeps _ _ _ _ (bodyKeeps entered)
    intro reached
    apply guard_keeps
    intro continuing
    exact (rest (continuing.write index (continuing.registers index + 1))).trans (Function.update_of_ne apart ..)

theorem execute_keeps (code : Stmt) (state : State) (register : Reg) (outside : register ∉ writes code) :
    (execute state code).after.registers register = state.registers register := by
  induction code generalizing state with
  | skip | ret => rfl
  | instruction code =>
    simp only [execute]
    split
    · rename_i after ran
      exact instruction_keeps code state after register outside ran
    · rfl
  | seq first second left right =>
    obtain ⟨firstOut, secondOut⟩ := Finset.notMem_union.mp outside
    exact then_keeps _ _ _ _ (left state firstOut) (fun next => right next secondOut)
  | branch condition yes no left right =>
    obtain ⟨yesOut, noOut⟩ := Finset.notMem_union.mp outside
    simp only [execute]
    split
    · exact left state yesOut
    · split
      · exact right state noOut
      · rfl
  | fund units =>
    simp only [execute, fund]
    split <;> rfl
  | counted index bound cap body preserve =>
    simp only [writes, Finset.mem_insert, not_or] at outside
    simp only [execute]
    split
    · rfl
    · exact (loop_keeps _ _ _ _ outside.1 (fun next => preserve next outside.2) _ _).trans
        (Function.update_of_ne outside.1 ..)
  | early index bound condition cap body preserve =>
    simp only [writes, Finset.mem_insert, not_or] at outside
    simp only [execute]
    split
    · rfl
    · exact (loop_keeps _ _ _ _ outside.1 (fun next => preserve next outside.2) _ _).trans
        (Function.update_of_ne outside.1 ..)

end Mettapedia.Machines.TIsa.P1WordFrame
