import Mathlib.Data.Nat.Basic

/-!
# Files region retirement

A terminal run loses publication permission while its started operation
remains in Files custody. Files clears the checked region at the dispatch
boundary, and the kernel uses its acknowledgment in the reuse guard.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.FilesRetirement

inductive Phase where
  | live | detached | cleared | acknowledged
  deriving DecidableEq, Repr

structure State where
  run : Nat
  phase : Phase
  active : Option Nat
  deriving DecidableEq, Repr

inductive Action where
  | beginIO (run request : Nat)
  | detach (run : Nat)
  | finishIO (run request : Nat)
  | clear (run : Nat) (viewChecked : Bool)
  | acknowledge (run : Nat)
  | reuse (newRun : Nat)
  deriving DecidableEq, Repr

def step (s : State) : Action → State
  | .beginIO run request =>
      if run = s.run ∧ s.phase = .live ∧ s.active = none then
        { s with active := some request }
      else s
  | .detach run =>
      if run = s.run ∧ s.phase = .live then { s with phase := .detached } else s
  | .finishIO run request =>
      if run = s.run ∧ s.active = some request then { s with active := none } else s
  | .clear run viewChecked =>
      if run = s.run ∧ s.phase = .detached ∧ s.active = none ∧ viewChecked = true then
        { s with phase := .cleared }
      else s
  | .acknowledge run =>
      if run = s.run ∧ s.phase = .cleared then { s with phase := .acknowledged } else s
  | .reuse newRun =>
      if s.phase = .acknowledged ∧ s.run < newRun then ⟨newRun, .live, none⟩ else s

def Valid (s : State) : Prop :=
  (s.phase = .cleared ∨ s.phase = .acknowledged) → s.active = none

theorem detach_retains_io (s : State) (run : Nat) :
    (step s (.detach run)).active = s.active := by
  simp only [step]
  split <;> rfl

theorem unrelated_receipt_preserves (s : State) (run request : Nat)
    (wrong : run ≠ s.run ∨ s.active ≠ some request) :
    step s (.finishIO run request) = s := by
  rcases wrong with wrong | wrong <;> simp [step, wrong]

theorem busy_refuses_clear (s : State) (run request : Nat) (viewChecked : Bool)
    (busy : s.active = some request) : step s (.clear run viewChecked) = s := by
  simp [step, busy]

theorem clear_requires_detached_settled_view (s : State) (run : Nat) (viewChecked : Bool)
    (changed : step s (.clear run viewChecked) ≠ s) :
    run = s.run ∧ s.phase = .detached ∧ s.active = none ∧ viewChecked = true := by
  by_contra h
  exact changed (by simp [step, h])

theorem valid_step (s : State) (action : Action) (valid : Valid s) : Valid (step s action) := by
  cases action <;> simp only [step] <;> split
  all_goals try exact valid
  all_goals simp_all [Valid]

theorem valid_trace (s : State) (actions : List Action) (valid : Valid s) :
    Valid (actions.foldl step s) := by
  induction actions generalizing s with
  | nil => exact valid
  | cons action rest ih =>
      exact ih (step s action) (valid_step s action valid)

theorem acknowledged_trace_has_no_active_io (run : Nat) (actions : List Action)
    (ready : (actions.foldl step ⟨run, .live, none⟩).phase = .acknowledged) :
    (actions.foldl step ⟨run, .live, none⟩).active = none :=
  valid_trace _ actions (by simp [Valid]) (Or.inr ready)

theorem reuse_requires_ack (s : State) (newRun : Nat)
    (changed : (step s (.reuse newRun)).run ≠ s.run) :
    s.phase = .acknowledged ∧ s.run < newRun := by
  by_contra h
  exact changed (by simp [step, h])

example :
    [Action.beginIO 7 5, .detach 7, .finishIO 6 5, .clear 7 true,
      .acknowledge 7, .reuse 8].foldl step ⟨7, .live, none⟩ =
      ⟨7, .detached, some 5⟩ := by decide

example :
    [Action.beginIO 7 5, .detach 7, .finishIO 7 5, .clear 7 false,
      .clear 7 true, .acknowledge 7, .reuse 8].foldl step ⟨7, .live, none⟩ =
      ⟨8, .live, none⟩ := by decide

#print axioms clear_requires_detached_settled_view
#print axioms acknowledged_trace_has_no_active_io
#print axioms reuse_requires_ack

end Mettapedia.Machines.Kernel.FilesRetirement
