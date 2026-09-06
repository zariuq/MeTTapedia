import Mettapedia.Languages.MeTTa.PrimeNeedCacheLaws

/-!
# A conservative candidate for language-local Need transitions

The reference machine and its action interface remain unchanged. An explicit
extension may intercept a running local control with one silent local step;
all other controls and unhandled local states use the actual reference step.
The silent step preserves the complete world and outer stack, and charges one
transition with no heap, receipt or allocation work.

Disabling interception preserves arbitrary reference specifications, ordered
bounded frontiers and answers exactly. This candidate supplies neither a new
source language nor termination of repeated administrative transitions. It is
not a change to Prime's default evaluator. In particular, an ordinary local
transition is not represented by a fabricated effect or fresh Need allocation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeNeedLocalSteps

open PrimeNeedReference

/-- A reference specification plus an explicit, optional local-control step.
Only running local controls are eligible for interception. -/
structure Extension
    (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*) where
  reference : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect
  localStep : Local → Option Local

section Core

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}

def ofReference
    (reference : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Extension Origin Local Resume Rule Value StableFault RetryableFault Effect :=
  ⟨reference, fun _ => none⟩

/-- One candidate transition; protocol states are delegated unchanged. -/
def step
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  match machine.control with
  | .run state stack =>
      match extension.localStep state with
      | some next => [finished machine machine.world (.run next stack) 0 0 0 0]
      | none => PrimeNeedReference.step extension.reference machine
  | _ => PrimeNeedReference.step extension.reference machine

def advance
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  match step extension machine with
  | [] => [machine]
  | next => next

/-- The same ordered-frontier policy as the reference driver, with the
candidate one-step operation. An unfinished state is retained, not refuted. -/
def runFrontier
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Nat → List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) →
      List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
  | 0, states => states
  | fuel + 1, states =>
      if states.all isHalted then states
      else runFrontier extension fuel (states.flatMap (advance extension))

def answers
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List (Produced Value StableFault RetryableFault) :=
  (runFrontier extension fuel [machine]).filterMap haltedOutcome

variable
  (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
  (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)

theorem step_local {state next : Local} {stack : List (Frame Resume)}
    (control : machine.control = .run state stack)
    (selected : extension.localStep state = some next) :
    step extension machine =
      [finished machine machine.world (.run next stack) 0 0 0 0] := by
  simp only [step, control, selected]

theorem step_unhandled {state : Local} {stack : List (Frame Resume)}
    (control : machine.control = .run state stack)
    (unhandled : extension.localStep state = none) :
    step extension machine = PrimeNeedReference.step extension.reference machine := by
  simp only [step, control, unhandled]

theorem step_force {cell : CellId} {stack : List (Frame Resume)}
    (control : machine.control = .force cell stack) :
    step extension machine = PrimeNeedReference.step extension.reference machine := by
  simp only [step, control]

theorem step_returned {outcome : Produced Value StableFault RetryableFault}
    {stack : List (Frame Resume)} (control : machine.control = .returned outcome stack) :
    step extension machine = PrimeNeedReference.step extension.reference machine := by
  simp only [step, control]

theorem step_halted {outcome : Produced Value StableFault RetryableFault}
    (control : machine.control = .halted outcome) : step extension machine = [] := by
  simp only [step, control, PrimeNeedReference.step]

/-- A silent successor retains the entire world, not just its native answer
or heap; ownership, paths and causal receipt data are all unchanged. -/
theorem local_successor_exact {state next : Local} {stack : List (Frame Resume)}
    {successor : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (control : machine.control = .run state stack)
    (selected : extension.localStep state = some next)
    (member : successor ∈ step extension machine) :
    successor.world = machine.world ∧ successor.control = .run next stack ∧
      successor.work = machine.work.bump 0 0 0 0 := by
  rw [step_local extension machine control selected, List.mem_singleton] at member
  subst successor
  exact ⟨rfl, rfl, rfl⟩

theorem local_successor_work {state next : Local} {stack : List (Frame Resume)}
    {successor : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (control : machine.control = .run state stack)
    (selected : extension.localStep state = some next)
    (member : successor ∈ step extension machine) :
    successor.work.transitions = machine.work.transitions + 1 ∧
    successor.work.heapLookups = machine.work.heapLookups ∧
    successor.work.heapUpdates = machine.work.heapUpdates ∧
    successor.work.receiptAppends = machine.work.receiptAppends ∧
    successor.work.allocations = machine.work.allocations := by
  rw [(local_successor_exact extension machine control selected member).2.2]
  simp only [Work.bump, Nat.add_zero, and_self]

/-- Every successor is either a world-preserving local step or an actual
reference successor. This is also the transfer boundary for heap invariants. -/
theorem successor_world_eq_or_reference
    {successor : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : successor ∈ step extension machine) :
    successor.world = machine.world ∨
      successor ∈ PrimeNeedReference.step extension.reference machine := by
  cases control : machine.control with
  | run state stack =>
      cases selected : extension.localStep state with
      | none => exact Or.inr (by simpa only [step, control, selected] using member)
      | some next =>
          exact Or.inl (local_successor_exact extension machine control selected member).1
  | force cell stack => exact Or.inr (by simpa only [step, control] using member)
  | returned outcome stack => exact Or.inr (by simpa only [step, control] using member)
  | halted outcome => exact Or.inr (by simpa only [step, control] using member)

theorem step_preserves_completed
    {successor : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : successor ∈ step extension machine)
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (lookup : machine.world.heap.lookup cell = some record)
    (completed : PrimeNeedCacheLaws.Cache.Completed record.cache) :
    successor.world.heap.lookup cell = some record := by
  rcases successor_world_eq_or_reference extension machine member with same | reference
  · simpa only [same] using lookup
  · exact PrimeNeedCacheLaws.step_preserves_completed extension.reference machine successor
      reference lookup completed

theorem force_cached_value_step {cell : CellId} {stack : List (Frame Resume)}
    {origin : Origin} {value : Value}
    (control : machine.control = .force cell stack)
    (lookup : machine.world.heap.lookup cell = some ⟨origin, .value value⟩) :
    step extension machine =
      [finished machine (recorded machine.world (.observe cell (.value value)))
        (.returned (.value value) stack) 1 0 1 0] := by
  rw [step_force extension machine control]
  exact PrimeNeedCacheLaws.force_cached_value_step extension.reference machine control lookup

variable (reference : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

@[simp] theorem step_ofReference :
    step (ofReference reference) machine = PrimeNeedReference.step reference machine := by
  cases control : machine.control <;> simp only [step, control, ofReference]

@[simp] theorem advance_ofReference :
    advance (ofReference reference) machine = PrimeNeedReference.advance reference machine := by
  cases result : PrimeNeedReference.step reference machine <;>
    simp only [advance, step_ofReference, PrimeNeedReference.advance, result]

/-- Exact list equality preserves ordering, multiplicity, unfinished controls,
worlds and work for every reference specification, not merely one example. -/
@[simp] theorem runFrontier_ofReference (fuel : Nat)
    (states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    runFrontier (ofReference reference) fuel states =
      PrimeNeedReference.runFrontier reference fuel states := by
  induction fuel generalizing states with
  | zero => rfl
  | succ fuel ih =>
      have sameAdvance : advance (ofReference reference) = PrimeNeedReference.advance reference :=
        funext (fun state => advance_ofReference state reference)
      simp only [runFrontier, PrimeNeedReference.runFrontier, sameAdvance, ih]

@[simp] theorem answers_ofReference (fuel : Nat) :
    answers (ofReference reference) fuel machine = PrimeNeedReference.answers reference fuel machine := by
  simp only [answers, PrimeNeedReference.answers, runFrontier_ofReference]

end Core

namespace Examples

abbrev ExampleMachine := Machine Unit Nat Unit Unit Nat Unit Unit Unit
abbrev ExampleExtension := Extension Unit Nat Unit Unit Nat Unit Unit Unit

def world : World Unit Unit Nat Unit Unit Unit :=
  ⟨0, [], Heap.empty, ReceiptGraph.empty, 0, 0⟩

def reference : Spec Unit Nat Unit Unit Nat Unit Unit Unit where
  alternatives := fun _ => [((), 0)]
  action := fun state => .done (.value state)
  afterDemand := fun _ _ => 0
  afterAllocation := fun _ _ => 0

/-- Two actual silent controls, followed by the unchanged return protocol. -/
def candidate : ExampleExtension where
  reference := reference
  localStep := fun state => if state < 2 then some (state + 1) else none

def initial : ExampleMachine := ⟨world, .run 0 [], {}⟩

theorem silent_controls_reach_answer : answers candidate 4 initial = [.value 2] := by
  decide

theorem reference_answer_is_different : PrimeNeedReference.answers reference 4 initial = [.value 0] := by
  decide

/-- Exhausted fuel leaves a real running control, not a false outcome. -/
theorem unfinished_frontier :
    (runFrontier candidate 2 [initial]).map (fun machine => machine.control) = [.run 2 []] := by
  rfl

theorem unfinished_has_no_answer_yet : answers candidate 2 initial = [] := by
  decide

theorem silent_frontier_world :
    (runFrontier candidate 2 [initial]).map (fun machine => machine.world) = [world] := by
  rfl

theorem silent_frontier_work :
    (runFrontier candidate 2 [initial]).map (fun machine => machine.work) =
      [⟨2, 0, 0, 0, 0⟩] := by
  decide

def performReference : Spec Unit Nat Unit Unit Nat Unit Unit Unit :=
  { reference with action := fun _ => .perform () 1 }

def allocateReference : Spec Unit Nat Unit Unit Nat Unit Unit Unit :=
  { reference with action := fun _ => .allocate () (), afterAllocation := fun _ _ => 1 }

/-- These observations retain actual receipt creation and fresh-cell state. -/
def retainedObservation (machine : ExampleMachine) : Nat × Nat :=
  (machine.world.receipts.nodes.length, machine.world.nextCell)

theorem silent_observation : (step candidate initial).map retainedObservation = [(0, 0)] := by
  decide

theorem perform_observation :
    (PrimeNeedReference.step performReference initial).map retainedObservation = [(1, 0)] := by
  decide

theorem allocation_observation :
    (PrimeNeedReference.step allocateReference initial).map retainedObservation = [(1, 1)] := by
  decide

theorem silent_not_perform :
    (step candidate initial).map retainedObservation ≠
      (PrimeNeedReference.step performReference initial).map retainedObservation := by
  rw [silent_observation, perform_observation]
  decide

theorem silent_not_allocate :
    (step candidate initial).map retainedObservation ≠
      (PrimeNeedReference.step allocateReference initial).map retainedObservation := by
  rw [silent_observation, allocation_observation]
  decide

end Examples

#print axioms local_successor_exact
#print axioms local_successor_work
#print axioms step_preserves_completed
#print axioms force_cached_value_step
#print axioms runFrontier_ofReference
#print axioms answers_ofReference
#print axioms Examples.silent_controls_reach_answer
#print axioms Examples.unfinished_frontier
#print axioms Examples.silent_not_perform
#print axioms Examples.silent_not_allocate

end Mettapedia.Languages.MeTTa.PrimeNeedLocalSteps
