import Mettapedia.Machines.SharedContinuation

/-!
# A divergent earlier alternative in the actual shared coordinator

The program is an instance of the existing shared-continuation machine, not
another evaluator. Its first tail call loops forever; its later return remains
retained but is never visited by the fixed depth-first scheduler. This is a
scheduler boundary, not a claim that the nonrecursive scoped Need fragment
diverges from an admitted empty heap.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.OrderedPathsControls

open Mettapedia.Machines.SharedContinuation

inductive Control where
  | start | loop | answer
  deriving DecidableEq, Repr

inductive Call where
  | alternatives | again
  deriving DecidableEq, Repr

def program : Program Unit Control Call Empty Nat where
  inspect
    | .start => .tail .alternatives
    | .loop => .tail .again
    | .answer => .ret 7
  branches context
    | .alternatives => [(context, .loop), (context, .answer)]
    | .again => [(context, .loop)]
  resume _ impossible _ := nomatch impossible

def start : State Unit Control Empty Nat := ⟨[⟨(), .start, []⟩], []⟩
def blocked : State Unit Control Empty Nat :=
  ⟨[⟨(), .loop, []⟩, ⟨(), .answer, []⟩], []⟩

theorem both_alternatives_are_retained : step program start = blocked := rfl

theorem loop_never_discards_the_later_alternative : step program blocked = blocked := rfl

theorem blocked_forever (count : Nat) : (step program)^[count] blocked = blocked := by
  induction count with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply', ih, loop_never_discards_the_later_alternative]

theorem earlier_divergence_prevents_all_later_answers (count : Nat) :
    (step program)^[count + 1] start = blocked := by
  rw [Function.iterate_succ_apply, both_alternatives_are_retained, blocked_forever]

theorem selected_later_return_finishes :
    step program (⟨[⟨(), .answer, []⟩], []⟩ : State Unit Control Empty Nat) =
      ⟨[], [((), 7)]⟩ := rfl

theorem no_depth_first_completion (count : Nat) :
    ((step program)^[count] start).frontier ≠ [] := by
  cases count with
  | zero => simp [start]
  | succ count => rw [earlier_divergence_prevents_all_later_answers]; simp [blocked]

end Mettapedia.Machines.BranchLocalNeed.OrderedPathsControls
