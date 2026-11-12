import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Stopping an existing machine at a retained checkpoint

The controller checks a boundary before taking the next original step.
Original requests, verdicts, events and residual states remain distinct.
A checkpoint is a new request, not successful program completion.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Checkpoint

open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {State Event Verdict Request : Type}

def machine (original : Machine State Event Verdict Request) (stop : State → Bool) :
    Machine State Event Verdict (Unit ⊕ Request) where
  step state :=
    if stop state then some (.call (.inl ()) state)
    else (original.step state).map (Transition.relabel id id Sum.inr)

theorem boundary_step (original : Machine State Event Verdict Request) (stop : State → Bool)
    (state : State) (atBoundary : stop state = true) :
    (machine original stop).step state = some (.call (.inl ()) state) := by
  simp only [machine, atBoundary, if_true]

theorem boundary_run (original : Machine State Event Verdict Request) (stop : State → Bool)
    (state : State) (atBoundary : stop state = true) (fuel : Nat) :
    (machine original stop).run (fuel + 1) state = ([], .suspended (.inl ()) state) :=
  (machine original stop).run_succ_call (boundary_step original stop state atBoundary)

theorem interior_step (original : Machine State Event Verdict Request) (stop : State → Bool)
    (state : State) (inside : stop state = false) :
    (machine original stop).step state =
      (original.step state).map (Transition.relabel id id Sum.inr) := by
  simp only [machine, inside, Bool.false_eq_true, if_false]

def Interior (original : Machine State Event Verdict Request) (stop : State → Bool)
    (before after : State) : Prop :=
  stop before = false ∧
    (original.step before = some (.silent after) ∨
      ∃ events, original.step before = some (.publish events after))

/-- Reaching a checkpoint earns a path of actual original transitions.
The controller cannot manufacture a checkpoint from a verdict or a request. -/
theorem boundary_path (original : Machine State Event Verdict Request) (stop : State → Bool)
    (fuel : Nat) (before after : State)
    (reached : ((machine original stop).run fuel before).2 = .suspended (.inl ()) after) :
    Relation.ReflTransGen (Interior original stop) before after ∧ stop after = true := by
  induction fuel generalizing before with
  | zero => cases reached
  | succ fuel ih =>
      cases checked : stop before with
      | true =>
          have outcome := congrArg Prod.snd (boundary_run original stop before checked fuel)
          rw [outcome] at reached
          cases Outcome.suspended.inj reached |>.2
          exact ⟨.refl, checked⟩
      | false =>
          cases advanced : original.step before with
          | none => simp [Machine.run, machine, checked, advanced] at reached
          | some action =>
              cases action with
              | silent next =>
                  have nextReached : ((machine original stop).run fuel next).2 = .suspended (.inl ()) after := by
                    simpa only [Machine.run, machine, checked, Bool.false_eq_true, if_false, advanced,
                      Option.map_some, Transition.relabel] using reached
                  obtain ⟨path, atBoundary⟩ := ih next nextReached
                  exact ⟨.head ⟨checked, .inl advanced⟩ path, atBoundary⟩
              | publish events next =>
                  have nextReached : ((machine original stop).run fuel next).2 = .suspended (.inl ()) after := by
                    simpa only [Machine.run, machine, checked, Bool.false_eq_true, if_false, advanced,
                      Option.map_some, Transition.relabel] using reached
                  obtain ⟨path, atBoundary⟩ := ih next nextReached
                  exact ⟨.head ⟨checked, .inr ⟨events, advanced⟩⟩ path, atBoundary⟩
              | finish verdict | fail events | call request saved =>
                  simp [Machine.run, machine, checked, advanced, Transition.relabel] at reached

end Mettapedia.Machines.Checkpoint
