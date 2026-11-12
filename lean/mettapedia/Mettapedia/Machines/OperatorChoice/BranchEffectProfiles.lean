import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.NormNum

/-!
# Ordered effects, branch summaries and independent reorderings

Unordered query answers do not specify an effect observer. This module
compares a full output sequence, a bag of per-branch output sequences, and
execution modulo adjacent commuting actions. The branch summary loses
information needed by ordinary ordered output. The commuting quotient has
a positive execution law because independence includes the complete state
being observed.

The examples use finite completed executions. They do not fix PeTTa or HE's
scheduler, buffer effects, or erase interaction and interruption boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.BranchEffectProfiles

open Mettapedia.GSLT.Core.NonFactorization

structure Event where
  branch : Nat
  message : Nat
  deriving DecidableEq, Repr

def stdout (trace : List Event) : List Nat := trace.map Event.message

def branchTrace (trace : List Event) (branch : Nat) : List Nat :=
  trace.filterMap fun event => if event.branch = branch then some event.message else none

def branchBag (branches : List Nat) (trace : List Event) : Multiset (List Nat) :=
  (branches.map (branchTrace trace) : Multiset (List Nat))

def firstThenSecond : List Event := [⟨0, 10⟩, ⟨1, 20⟩]
def secondThenFirst : List Event := [⟨1, 20⟩, ⟨0, 10⟩]

theorem branch_summary_agrees :
    branchBag [0, 1] firstThenSecond = branchBag [0, 1] secondThenFirst := rfl

theorem global_output_differs : stdout firstThenSecond ≠ stdout secondThenFirst := by decide

/-- Even internally ordered branch logs cannot recover the chronology
observed by ordinary output. A coarser test needs a different declared observer. -/
theorem ordered_output_does_not_factor_through_branch_bag :
    ¬ Factors (branchBag [0, 1]) stdout :=
  (show NonTrivialFiber (branchBag [0, 1]) stdout from
    ⟨firstThenSecond, secondThenFirst, branch_summary_agrees, global_output_differs⟩).not_factors

/-- A deliberately unordered output observer identifies the two histories.
This is an explicit change of observation, not a consequence of bag answers. -/
theorem unordered_output_agrees :
    (stdout firstThenSecond : Multiset Nat) = (stdout secondThenFirst : Multiset Nat) := by
  decide

variable {Action State : Type}

def run (step : Action → State → State) : List Action → State → State
  | [], state => state
  | action :: rest, state => run step rest (step action state)

theorem run_append (step : Action → State → State) (first last : List Action) (state : State) :
    run step (first ++ last) state = run step last (run step first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons action rest ih => exact ih (step action state)

/-- State includes every component promised by the selected observer,
including ordered output if that is part of the contract. -/
def Commutes (step : Action → State → State) (first second : Action) : Prop :=
  ∀ state, step second (step first state) = step first (step second state)

inductive Swap (step : Action → State → State) : List Action → List Action → Prop where
  | exchange (before after : List Action) (first second : Action)
      (independent : Commutes step first second) :
      Swap step (before ++ first :: second :: after) (before ++ second :: first :: after)

theorem swap_preserves_execution (step : Action → State → State)
    {first last : List Action} (swapped : Swap step first last) (state : State) :
    run step first state = run step last state := by
  cases swapped with
  | exchange before after first second independent =>
      simp only [run_append, run]
      rw [independent]

theorem equivalent_preserves_execution (step : Action → State → State)
    {first last : List Action} (equivalent : Relation.EqvGen (Swap step) first last)
    (state : State) : run step first state = run step last state := by
  induction equivalent with
  | rel _ _ swapped => exact swap_preserves_execution step swapped state
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ firstIH lastIH => exact firstIH.trans lastIH

def traceSetoid (step : Action → State → State) : Setoid (List Action) where
  r := Relation.EqvGen (Swap step)
  iseqv := ⟨fun value => .refl value, fun {first last} proof => .symm first last proof,
    fun {first middle last} left right => .trans first middle last left right⟩

def causalExecution (step : Action → State → State) :
    Quotient (traceSetoid step) → State → State :=
  Quotient.lift (run step) fun _ _ equivalent =>
    funext fun state => equivalent_preserves_execution step equivalent state

def printMessage (message : Nat) (output : List Nat) : List Nat := output ++ [message]

theorem distinct_prints_do_not_commute : ¬ Commutes printMessage 10 20 := by
  intro independent
  have same := independent []
  have different : ([10, 20] : List Nat) ≠ [20, 10] := by decide
  exact different same

/-- Keeping output in the state prevents the causal quotient from erasing
the order of externally visible printing. -/
theorem distinct_prints_have_distinct_causal_traces :
    (⟦[10, 20]⟧ : Quotient (traceSetoid printMessage)) ≠ ⟦[20, 10]⟧ := by
  intro same
  have equal := congrFun (congrArg (causalExecution printMessage) same) []
  have different : ([10, 20] : List Nat) ≠ [20, 10] := by decide
  exact different equal

def write (operation : Nat × Nat) (store : Nat → Nat) : Nat → Nat :=
  Function.update store operation.1 operation.2

theorem disjoint_writes_commute (left right leftValue rightValue : Nat)
    (different : left ≠ right) : Commutes write (left, leftValue) (right, rightValue) := by
  intro store
  funext address
  by_cases atLeft : address = left
  · subst address
    simp [write, different]
  · by_cases atRight : address = right
    · subst address
      simp [write, Ne.symm different]
    · simp [write, atLeft, atRight]

theorem disjoint_writes_have_one_causal_trace (left right leftValue rightValue : Nat)
    (different : left ≠ right) :
    (⟦[(left, leftValue), (right, rightValue)]⟧ : Quotient (traceSetoid write)) =
      ⟦[(right, rightValue), (left, leftValue)]⟧ := by
  apply Quotient.sound
  exact .rel _ _ (.exchange [] [] _ _
    (disjoint_writes_commute left right leftValue rightValue different))

theorem shared_writes_do_not_commute : ¬ Commutes write (0, 1) (0, 2) := by
  intro independent
  have same := congrFun (independent (fun _ => 0)) 0
  norm_num [write] at same

end Mettapedia.Machines.OperatorChoice.BranchEffectProfiles
