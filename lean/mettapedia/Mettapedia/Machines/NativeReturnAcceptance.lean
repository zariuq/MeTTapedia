import Mettapedia.Machines.NativeCallReturn
import Mettapedia.Machines.RuntimePlumbing.DependencyStamps

/-!
# Acceptance of an ordered return by its live receiver

A receiver binding denotes the complete continuation for one invocation.
Rebinding or retiring it advances its version, even if the replacement has
equal contents. Acceptance uses the receiver and source validation at one
observation and consumes the offered occurrence positions in that step.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeReturnAcceptance

open NativeCallReturn (Cursor Returned advance residual)
open RuntimePlumbing.DependencyStamps (Memory Advances)

variable {Value Fault Delay Context : Type}

abbrev Binding (Context : Type) := Memory Unit (Option Context)

def accept (programValid : Bool) (captured live : Binding Context)
    (offered allowance : Nat) (cursor : Cursor Value Fault Delay Context) :
    Option (List (Returned Value Fault Delay Context)) × Cursor Value Fault Delay Context :=
  if programValid && decide (captured.stamp () = live.stamp ()) && decide (offered = cursor.position) then
    let chunk := advance allowance cursor
    (some chunk.1, chunk.2)
  else (none, cursor)

private theorem read_position {cursor next : Cursor Value Fault Delay Context}
    {item : Returned Value Fault Delay Context}
    (lent : NativeCallReturn.read cursor = .returned item next) :
    next.source = cursor.source ∧ next.context = cursor.context ∧ next.position = cursor.position + 1 := by
  rcases cursor with ⟨source, context, position⟩
  cases source <;> simp only [NativeCallReturn.read, reduceCtorEq] at lent
  case one packet =>
    split at lent
    · rename_i start
      cases lent
      simp [start]
    · cases lent
  case frontier role words =>
    split at lent
    · cases lent
    · cases lent
      exact ⟨rfl, rfl, rfl⟩

theorem advance_keeps_binding (allowance : Nat) (cursor : Cursor Value Fault Delay Context) :
    let next := (advance allowance cursor).2
    next.source = cursor.source ∧ next.context = cursor.context ∧
      next.position = cursor.position + (advance allowance cursor).1.length := by
  induction allowance generalizing cursor with
  | zero => simp [advance]
  | succ rest ih =>
    cases step : NativeCallReturn.read cursor with
    | stopped reason => simp [advance, step]
    | returned item next =>
      obtain ⟨source, context, position⟩ := read_position step
      obtain ⟨restSource, restContext, restPosition⟩ := ih next
      simp only [advance, step, List.length_cons]
      exact ⟨restSource.trans source, restContext.trans context, by rw [restPosition, position]; omega⟩

private theorem accepted_advance {programValid : Bool} {captured live : Binding Context}
    {offered allowance : Nat} {cursor next : Cursor Value Fault Delay Context}
    {items : List (Returned Value Fault Delay Context)}
    (accepted : accept programValid captured live offered allowance cursor = (some items, next)) :
    programValid = true ∧ captured.stamp () = live.stamp () ∧ offered = cursor.position ∧
      advance allowance cursor = (items, next) := by
  unfold accept at accepted
  split at accepted
  · rename_i valid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
    exact ⟨valid.1.1, valid.1.2, valid.2, Prod.ext (Option.some.inj (Prod.mk.inj accepted).1)
      (Prod.mk.inj accepted).2⟩
  · cases (Prod.mk.inj accepted).1

theorem accepted_exact (programValid : Bool) (captured live : Binding Context)
    (offered allowance : Nat) (cursor next : Cursor Value Fault Delay Context)
    (items : List (Returned Value Fault Delay Context))
    (capturedContext : captured.value () = some cursor.context) (window : Advances captured live)
    (accepted : accept programValid captured live offered allowance cursor = (some items, next)) :
    programValid = true ∧ live.value () = some cursor.context ∧ offered = cursor.position ∧
      next.source = cursor.source ∧ next.context = cursor.context ∧ next.position = cursor.position + items.length ∧
      items = (residual cursor).1.take allowance ∧
      residual next = ((residual cursor).1.drop allowance, (residual cursor).2) := by
  obtain ⟨program, stamp, position, advanced⟩ := accepted_advance accepted
  have sameContext : live.value () = some cursor.context :=
    ((window ()).2 stamp).symm.trans capturedContext
  have keeps := advance_keeps_binding allowance cursor
  have ordered := NativeCallReturn.advance_exact allowance cursor
  rw [advanced] at keeps ordered
  exact ⟨program, sameContext, position, keeps.1, keeps.2.1, keeps.2.2, ordered.1, ordered.2⟩

theorem bad_position_keeps_work (programValid : Bool) (captured live : Binding Context)
    (offered allowance : Nat) (cursor : Cursor Value Fault Delay Context)
    (different : offered ≠ cursor.position) :
    accept programValid captured live offered allowance cursor = (none, cursor) := by
  simp [accept, different]

theorem changed_receiver_keeps_work (programValid : Bool) (captured live : Binding Context)
    (offered allowance : Nat) (cursor : Cursor Value Fault Delay Context)
    (window : Advances captured live) (changed : captured.value () ≠ live.value ()) :
    accept programValid captured live offered allowance cursor = (none, cursor) := by
  have newer : captured.stamp () ≠ live.stamp () := fun equal => changed ((window ()).2 equal)
  simp [accept, newer]

theorem accepted_nonempty_invalidates_offer (programValid : Bool) (captured live : Binding Context)
    (offered allowance : Nat) (cursor next : Cursor Value Fault Delay Context)
    (items : List (Returned Value Fault Delay Context)) (nonempty : items ≠ [])
    (accepted : accept programValid captured live offered allowance cursor = (some items, next))
    (again : Bool) (before after : Binding Context) (budget : Nat) :
    accept again before after offered budget next = (none, next) := by
  obtain ⟨_, _, atPosition, delivered⟩ := accepted_advance accepted
  have keeps := advance_keeps_binding allowance cursor
  rw [delivered] at keeps
  have advanced := keeps.2.2
  change next.position = cursor.position + items.length at advanced
  have positive : 0 < items.length := List.length_pos_iff.mpr nonempty
  exact bad_position_keeps_work again before after offered budget next (by omega)

/-- Two accepted slices consume one ordered prefix together. Their validation
observations may differ and neither retries the accepted portion of the other. -/
theorem accepted_slices_compose {firstValid secondValid : Bool} {captured firstLive secondLive : Binding Context}
    {firstPosition secondPosition firstLimit secondLimit : Nat}
    {cursor middle next : Cursor Value Fault Delay Context}
    {firstItems secondItems : List (Returned Value Fault Delay Context)}
    (first : accept firstValid captured firstLive firstPosition firstLimit cursor = (some firstItems, middle))
    (second : accept secondValid captured secondLive secondPosition secondLimit middle = (some secondItems, next)) :
    advance (firstLimit + secondLimit) cursor = (firstItems ++ secondItems, next) := by
  rw [NativeCallReturn.advance_add, (accepted_advance first).2.2.2]
  change ((firstItems ++ (advance secondLimit middle).1, (advance secondLimit middle).2)) = _
  rw [(accepted_advance second).2.2.2]

namespace Controls

private abbrev TestCursor := Cursor Nat Unit Unit Nat

private def bound : Binding Nat := ⟨fun _ => some 5, fun _ => 0⟩
private def repeatTwo : TestCursor := ⟨.frontier .completed #[7, 7], 5, 0⟩

theorem duplicate_values_require_two_positions :
    let first := accept true bound bound 0 1 repeatTwo
    let second := accept true bound bound 1 1 first.2
    first.1 = some [(5, .value .completed 7)] ∧
      accept true bound bound 0 1 first.2 = (none, first.2) ∧
      second.1 = some [(5, .value .completed 7)] ∧ second.2.position = 2 := by decide +kernel

theorem rebind_to_equal_contents_expires_old_offer :
    let rebound := RuntimePlumbing.DependencyStamps.write bound () (some 5)
    rebound.value () = bound.value () ∧
      accept true bound rebound 0 1 repeatTwo = (none, repeatTwo) := by decide +kernel

theorem stale_program_leaves_earned_work :
    accept false bound bound 0 1 repeatTwo = (none, repeatTwo) := rfl

theorem exhausted_is_an_accepted_empty_slice :
    let finished : TestCursor := {repeatTwo with position := 2}
    accept true bound bound 2 1 finished = (some [], finished) := by decide +kernel

end Controls

end Mettapedia.Machines.NativeReturnAcceptance
