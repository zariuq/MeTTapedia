import Mettapedia.Machines.OccurrenceMachine

/-!
# Completion and interruption observations

An answer list does not determine whether exploration is complete. A bounded
run can emit answers while leaving live work, and a resource interruption can
occur after answers have already been emitted.

This module keeps three cases separate:

* exhaustive completion;
* an explicit live frontier left by a transition-depth cut;
* an external resource interruption, whose frontier may not be exported.

The four external interruption reasons mirror the distinctions exposed by the
native evaluator API. No refinement to that API is claimed here.
-/

namespace Mettapedia.Machines

/-- Resource reasons reported independently of the answer frontier. A depth
cut is not included: it carries an explicit abstract-machine frontier below. -/
inductive ResourceInterruption where
  | fuelExhausted
  | cancelled
  | stackExhausted
  | capacityExhausted
  deriving DecidableEq, Repr

/-- Why a run stopped. `depthCut` carries nonempty live work. An external
interruption does not pretend that the native runtime exported that work. -/
inductive RunStop (State : Type) where
  | complete
  | depthCut
      (pending : List (State × List Nat))
      (nonempty : pending ≠ [])
  | interrupted (reason : ResourceInterruption)

namespace RunStop

variable {State : Type}

/-- The frontier exported specifically by an exhaustive transition-depth cut.
An empty result for an external interruption means "not exported", not "no
work remains". -/
def depthFrontier : RunStop State → List (State × List Nat)
  | .depthCut pending _ => pending
  | .complete | .interrupted _ => []

/-- The external interruption reason, when the stop was resource-driven. -/
def externalInterruption : RunStop State → Option ResourceInterruption
  | .interrupted reason => some reason
  | .complete | .depthCut _ _ => none

@[simp] theorem depthFrontier_complete :
    (complete : RunStop State).depthFrontier = [] := rfl

@[simp] theorem depthFrontier_depthCut
    (pending : List (State × List Nat)) (h : pending ≠ []) :
    (depthCut pending h).depthFrontier = pending := rfl

@[simp] theorem depthFrontier_interrupted (reason : ResourceInterruption) :
    (interrupted reason : RunStop State).depthFrontier = [] := rfl

@[simp] theorem externalInterruption_complete :
    (complete : RunStop State).externalInterruption = none := rfl

@[simp] theorem externalInterruption_depthCut
    (pending : List (State × List Nat)) (h : pending ≠ []) :
    (depthCut pending h).externalInterruption = none := rfl

@[simp] theorem externalInterruption_interrupted
    (reason : ResourceInterruption) :
    (interrupted reason : RunStop State).externalInterruption = some reason :=
  rfl

end RunStop

/-- Answer occurrences together with the reason expansion stopped. -/
structure RunObservation (State Answer : Type) where
  answers : List (Answer × List Nat)
  stop : RunStop State

namespace RunObservation

variable {State Answer : Type}

/-- Erase transition certificates while retaining answer occurrences. -/
def answerOccurrences (observation : RunObservation State Answer) :
    List Answer :=
  observation.answers.map Prod.fst

/-- Forget occurrence order but retain multiplicity. -/
def answerBag (observation : RunObservation State Answer) : Multiset Answer :=
  observation.answerOccurrences

end RunObservation

namespace OccurrenceMachineCore

variable {Term State Answer : Type}

/-- Classify an exhaustive transition-depth expansion. An empty pending list
means the explored search is exhausted; otherwise the exact live frontier is
retained in the stop certificate. -/
def observeDepth (M : OccurrenceMachineCore Term State Answer)
    (depth : Nat) (state : State) : RunObservation State Answer :=
  let slice := M.expand depth state
  match slice.pending with
  | [] =>
      { answers := slice.answers
        stop := .complete }
  | first :: rest =>
      { answers := slice.answers
        stop := .depthCut (first :: rest) (by simp) }

/-- Completion classification does not alter or quotient answer occurrences. -/
@[simp] theorem observeDepth_answers
    (M : OccurrenceMachineCore Term State Answer)
    (depth : Nat) (state : State) :
    (M.observeDepth depth state).answers = M.answerTraces depth state := by
  cases h : M.pendingTraces depth state with
  | nil => simp [observeDepth, expand, h]
  | cons first rest => simp [observeDepth, expand, h]

/-- Completion classification preserves the exact answer-occurrence list. -/
@[simp] theorem observeDepth_answerOccurrences
    (M : OccurrenceMachineCore Term State Answer)
    (depth : Nat) (state : State) :
    (M.observeDepth depth state).answerOccurrences =
      M.answerOccurrences depth state := by
  simp [RunObservation.answerOccurrences, M.answerTraces_map_fst]

/-- Forgetting order after completion classification gives the same semantic
answer bag as forgetting order directly on the machine expansion. -/
@[simp] theorem observeDepth_answerBag
    (M : OccurrenceMachineCore Term State Answer)
    (depth : Nat) (state : State) :
    (M.observeDepth depth state).answerBag = M.answerBag depth state := by
  simp [RunObservation.answerBag, answerBag]

/-- The stop certificate retains exactly the pending depth frontier. -/
@[simp] theorem observeDepth_depthFrontier
    (M : OccurrenceMachineCore Term State Answer)
    (depth : Nat) (state : State) :
    (M.observeDepth depth state).stop.depthFrontier =
      M.pendingTraces depth state := by
  cases h : M.pendingTraces depth state with
  | nil => simp [observeDepth, expand, h]
  | cons first rest => simp [observeDepth, expand, h]

/-- A depth observation is complete exactly when no live state remains at the
cut. Stuck non-answer leaves count as exhausted, not pending. -/
theorem observeDepth_complete_iff
    (M : OccurrenceMachineCore Term State Answer)
    (depth : Nat) (state : State) :
    (M.observeDepth depth state).stop = .complete ↔
      M.pendingTraces depth state = [] := by
  cases h : M.pendingTraces depth state with
  | nil => simp [observeDepth, expand, h]
  | cons first rest => simp [observeDepth, expand, h]

/-- A depth-bound observation never fabricates an external interruption. -/
@[simp] theorem observeDepth_externalInterruption
    (M : OccurrenceMachineCore Term State Answer)
    (depth : Nat) (state : State) :
    (M.observeDepth depth state).stop.externalInterruption = none := by
  cases h : M.pendingTraces depth state with
  | nil => simp [observeDepth, expand, h]
  | cons first rest => simp [observeDepth, expand, h]

/-! ## Discriminators: answers do not determine completion -/

inductive PartialDuplicateState where
  | root
  | done
  | waiting
  | later
  deriving DecidableEq

/-- The first two transition occurrences finish with equal answers while a
third occurrence remains live at depth one. -/
def partialDuplicateExample :
    OccurrenceMachineCore Unit PartialDuplicateState Nat where
  load := fun _ => .root
  next
    | .root => [.done, .done, .waiting]
    | .waiting => [.later]
    | .done | .later => []
  answer
    | .done => some 7
    | .later => some 9
    | .root | .waiting => none
  answer_final := by
    intro state answer h
    cases state <;> simp_all

/-- These two runs expose exactly the same answer occurrences. -/
example :
    (duplicateExample.observeDepth 1 .root).answers =
      (partialDuplicateExample.observeDepth 1 .root).answers := rfl

/-- The two-answer run with no third branch is exhaustive. -/
example :
    (duplicateExample.observeDepth 1 .root).stop = .complete := rfl

/-- The equal-answer run with a third branch retains that branch explicitly. -/
example :
    (partialDuplicateExample.observeDepth 1 .root).stop.depthFrontier =
      [(.waiting, [2])] := rfl

/-- Consequently, equal answer occurrences do not imply equal completion. -/
example :
    (partialDuplicateExample.observeDepth 1 .root).stop ≠ .complete := by
  intro completed
  have noPending :=
    (partialDuplicateExample.observeDepth_complete_iff 1 .root).mp completed
  simp [partialDuplicateExample, pendingTraces] at noPending

/-- An externally interrupted run may already contain answers; those answers
do not turn the interruption into completion. -/
def interruptedAfterAnswer : RunObservation Unit Nat where
  answers := [(7, [])]
  stop := .interrupted .fuelExhausted

example : interruptedAfterAnswer.answers = [(7, [])] := rfl

example : interruptedAfterAnswer.stop.externalInterruption =
    some .fuelExhausted := rfl

example : interruptedAfterAnswer.stop ≠ .complete := by
  intro h
  cases h

end OccurrenceMachineCore

end Mettapedia.Machines
