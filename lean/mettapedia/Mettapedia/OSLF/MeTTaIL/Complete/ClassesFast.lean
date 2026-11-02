import Mettapedia.OSLF.MeTTaIL.Complete.Settled

/-! Completed class searches retain their clock while skipping exhausted
lanes. The result equals the ordinary round loop, including its counters,
representatives, entries and complete publication log. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Classes

open GeneralExecutionAdmission _root_.Mettapedia.OSLF.MeTTaIL.Syntax

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

def roundsFast : Nat → State plan → State plan
  | 0, state => state
  | work + 1, state =>
      if complete plan state then
        { state with round := state.round + (work + 1) }
      else roundsFast work (round plan bound expected state)

theorem roundsFast_eq_rounds (work : Nat) (state : State plan) :
    roundsFast plan bound expected work state = rounds plan bound expected work state := by
  induction work generalizing state with
  | zero => rfl
  | succ work ih =>
      by_cases done : complete plan state = true
      · simpa only [roundsFast, done, if_true] using
          (Settled.rounds_complete plan bound expected state done (work + 1)).symm
      · simpa only [roundsFast, done, Bool.false_eq_true, if_false, rounds] using
          ih (round plan bound expected state)

theorem roundsFast_complete (state : State plan) (done : complete plan state = true) (work : Nat) :
    roundsFast plan bound expected work state = { state with round := state.round + work } := by
  rw [roundsFast_eq_rounds, Settled.rounds_complete plan bound expected state done]

/-- Completion preserves the data, but positive work still changes the clock. -/
theorem roundsFast_complete_ne_self (state : State plan) (done : complete plan state = true)
    (work : Nat) (positive : 0 < work) : roundsFast plan bound expected work state ≠ state := by
  rw [roundsFast_complete plan bound expected state done work]
  intro same
  have clock := congrArg State.round same
  simp only at clock
  omega

#print axioms roundsFast_eq_rounds
#print axioms roundsFast_complete
#print axioms roundsFast_complete_ne_self

end Mettapedia.OSLF.MeTTaIL.Complete.Classes
