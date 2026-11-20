import Mettapedia.Machines.TIsa.P1WritePolicy

/-!
# Register and allowance effects of structured p1 code

A write policy protects any register outside its allowed set. Code without
funding sites preserves the allowance and the consumed debit, including on
an early return or a failed memory access.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1WordEffects

open P1Source P1WordExecution
open P1WritePolicy (Policy Closed)

theorem preserves_register (policy : Policy) (code : Stmt) (state : State)
    (admitted : policy.accepts code = true) (register : Reg) (unwritable : policy.register register = false) :
    (execute state code).after.registers register = state.registers register := by
  let holds : State → Prop := fun current => current.registers register = state.registers register
  have closed : Closed policy holds := by
    refine ⟨?_, fun _ _ _ _ _ _ known _ _ => known, fun _ _ known => known⟩
    intro current destination value known writes
    have different : register ≠ destination := by
      intro same
      rw [← same, unwritable] at writes
      cases writes
    change Function.update current.registers destination value register = state.registers register
    rw [Function.update_of_ne different]
    exact known
  exact closed.execute admitted (show holds state from rfl)

/-- A code fragment with no debit leaves both fields of the allowance
    unchanged. -/
def KeepsAllowance (before after : State) : Prop :=
  after.budget = before.budget ∧ after.spent = before.spent

theorem KeepsAllowance.trans {first middle last : State}
    (left : KeepsAllowance first middle) (right : KeepsAllowance middle last) :
    KeepsAllowance first last := ⟨right.1.trans left.1, right.2.trans left.2⟩

private theorem instruction_keeps (state : State) (op : Instr) :
    KeepsAllowance state (execute state (.instruction op)).after := by
  rw [execute]
  cases call : instruction state op with
  | error => exact ⟨rfl, rfl⟩
  | ok after =>
    change KeepsAllowance state after
    cases op
    case' load ty width region dst base displacement => cases width
    case' store width region base displacement source => cases width
    all_goals simp only [instruction, scalarInstruction, Instr.destination?] at call
    all_goals repeat' split at call
    all_goals cases call <;> exact ⟨rfl, rfl⟩

private theorem guard_keeps (state : State) (guard : Option Reg) (next : State → Flow)
    (kept : KeepsAllowance state (next state).after) :
    KeepsAllowance state (continueLoop state guard next).after := by
  cases guard with
  | none => exact kept
  | some register =>
    simp only [continueLoop]
    split
    · exact kept
    · split <;> exact ⟨rfl, rfl⟩

private theorem loop_keeps (body : State → Flow) (bodyKeeps : ∀ state, KeepsAllowance state (body state).after)
    (index : Reg) (guard : Option Reg) (remaining : Nat) (state : State) :
    KeepsAllowance state (loop body index guard remaining state).after := by
  induction remaining generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ rest ih =>
    unfold loop
    apply guard_keeps
    have first := bodyKeeps state
    cases transition : body state with
    | returned => rw [transition] at first; exact first
    | continuing reached =>
      rw [transition] at first
      change KeepsAllowance state (continueLoop reached guard fun next =>
        loop body index guard rest (next.write index (next.registers index + 1))).after
      apply first.trans
      apply guard_keeps
      exact (show KeepsAllowance reached (reached.write index _) from ⟨rfl, rfl⟩).trans (ih _)

theorem uncharged (code : Stmt) (state : State) (neutral : code.fundPoints = 0) :
    KeepsAllowance state (execute state code).after := by
  induction code generalizing state with
  | skip | ret => exact ⟨rfl, rfl⟩
  | instruction op => exact instruction_keeps state op
  | fund debit => cases neutral
  | seq first second firstIH secondIH =>
    obtain ⟨one, two⟩ := Nat.add_eq_zero_iff.mp neutral
    have kept := firstIH state one
    rw [execute]
    cases transition : execute state first with
    | returned => rw [transition] at kept; exact kept
    | continuing reached =>
      rw [transition] at kept
      exact kept.trans (secondIH reached two)
  | branch condition yes no yesIH noIH =>
    obtain ⟨one, two⟩ := Nat.add_eq_zero_iff.mp neutral
    rw [execute]
    split
    · exact yesIH state one
    · split
      · exact noIH state two
      · exact ⟨rfl, rfl⟩
  | counted index bound cap body ih =>
    rw [execute]
    split
    · exact ⟨rfl, rfl⟩
    · exact loop_keeps (execute · body) (fun current => ih current neutral) index none _ _
  | early index bound condition cap body ih =>
    rw [execute]
    split
    · exact ⟨rfl, rfl⟩
    · exact loop_keeps (execute · body) (fun current => ih current neutral) index (some condition) _ _

end Mettapedia.Machines.TIsa.P1WordEffects
