import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

/-!
# Constraint meanings, answer delivery and conservative extension controls

Two one-variable stores can have the same solution set while exposing
different operational replies. This refutes the inference from denotational
agreement alone to agreement of all clients. The stores are a finite control
example, not implementations of a general unifier.

A separate symbolic evaluator retains unknown heads as data. Adding a fresh
operation preserves old operation entries and the old-signature fragment,
but changes some terms that were already legal symbolic syntax. Thus the
domain of an extension theorem must be stated explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.ConstraintObservationControls

open Mettapedia.GSLT.Core.NonFactorization

namespace Delivery

inductive Frame where
  | binding (value : Nat)
  | residualEquation (value : Nat)
  deriving DecidableEq, Repr

def models : Frame → Set Nat
  | .binding value => {assignment | assignment = value}
  | .residualEquation value => {assignment | assignment = value}

inductive Reply where
  | value (value : Nat)
  | blocked
  | refuted
  deriving DecidableEq, Repr

/-- This client asks for an exposed binding, not for logical entailment. -/
def inspect : Frame → Reply
  | .binding value => .value value
  | .residualEquation _ => .blocked

theorem same_solutions (value : Nat) :
    models (.binding value) = models (.residualEquation value) := rfl

theorem different_delivery (value : Nat) :
    inspect (.binding value) ≠ inspect (.residualEquation value) := by
  intro impossible
  cases impossible

theorem solution_sets_do_not_determine_delivery : ¬ Factors models inspect :=
  (show NonTrivialFiber models inspect from
    ⟨.binding 1, .residualEquation 1, same_solutions 1, different_delivery 1⟩).not_factors

def normalize : Frame → Frame
  | .binding value => .binding value
  | .residualEquation value => .binding value

theorem normalization_preserves_solutions (frame : Frame) :
    models (normalize frame) = models frame := by cases frame <;> rfl

theorem normalization_changes_this_observer (value : Nat) :
    inspect (normalize (.residualEquation value)) ≠ inspect (.residualEquation value) := by
  intro impossible
  cases impossible

theorem blocked_is_not_refuted : Reply.blocked ≠ Reply.refuted := by decide

end Delivery

namespace Extension

inductive Term where
  | literal (value : Nat)
  | call (head : String) (argument : Term)
  deriving DecidableEq, Repr

def oldOperation : String → Term → Term
  | "inc", .literal value => .literal (value + 1)
  | head, argument => .call head argument

def extendedOperation (head : String) (argument : Term) : Term :=
  if head = "zero" then .literal 0 else oldOperation head argument

def oldEval : Term → Term
  | .literal value => .literal value
  | .call head argument => oldOperation head (oldEval argument)

def extendedEval : Term → Term
  | .literal value => .literal value
  | .call head argument => extendedOperation head (extendedEval argument)

theorem old_operation_entries_preserved (head : String) (argument : Term)
    (oldHead : head ≠ "zero") :
    extendedOperation head argument = oldOperation head argument := by
  simp [extendedOperation, oldHead]

theorem increment_entry_preserved (argument : Term) :
    extendedOperation "inc" argument = oldOperation "inc" argument := rfl

inductive OldFragment : Term → Prop where
  | literal (value : Nat) : OldFragment (.literal value)
  | call (head : String) (argument : Term) (oldHead : head ≠ "zero")
      (oldArgument : OldFragment argument) : OldFragment (.call head argument)

theorem conservative_on_old_fragment {term : Term} (old : OldFragment term) :
    extendedEval term = oldEval term := by
  induction old with
  | literal value => rfl
  | call head argument oldHead _ ih =>
      rw [extendedEval, oldEval, ih, old_operation_entries_preserved head _ oldHead]

/-- The newly interpreted head was already a legal symbolic term. -/
theorem old_symbolic_term_changes :
    oldEval (.call "zero" (.literal 7)) = .call "zero" (.literal 7) ∧
      extendedEval (.call "zero" (.literal 7)) = .literal 0 := by decide

theorem not_conservative_on_all_old_syntax : ¬ ∀ term, extendedEval term = oldEval term := by
  intro same
  have impossible := same (.call "zero" (.literal 7))
  have distinct : Term.literal 0 ≠ .call "zero" (.literal 7) := by decide
  exact distinct impossible

end Extension

end Mettapedia.Machines.OperatorChoice.ConstraintObservationControls
