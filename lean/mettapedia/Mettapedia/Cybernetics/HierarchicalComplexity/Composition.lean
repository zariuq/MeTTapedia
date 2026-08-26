import Mettapedia.Cybernetics.HierarchicalComplexity.Basic

/-!
# Binary composition, commutation, and hierarchical order

For two state transformations there are two schedules.  Their schedule
semantics is a chain exactly when the two composites agree at the initial
state, and a coordination exactly when they differ there.  Component-local
updates on a product state commute automatically; arbitrary interacting
updates do not.

This supplies the precise bridge between the Commons--Pekker permutation test
and operational composition.  "Interaction" by itself is not used as a
synonym for order sensitivity: the theorem asks whether the actual composites
commute.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity.Composition

open Mettapedia.Cybernetics.HierarchicalComplexity

universe uState uLeft uRight uOutcome uOccurrence

/-- Two named transformations and the state from which their schedules are
compared. -/
structure BinaryProcess (State : Type uState) where
  initial : State
  left : State → State
  right : State → State

namespace BinaryProcess

variable {State : Type uState}

/-- Execute left then right. -/
def leftThenRight (process : BinaryProcess State) : State :=
  process.right (process.left process.initial)

/-- Execute right then left. -/
def rightThenLeft (process : BinaryProcess State) : State :=
  process.left (process.right process.initial)

/-- The two schedules are distinguished by which named transformation occurs
first. -/
def scheduleSemantics (process : BinaryProcess State) :
    ScheduleSemantics (Fin 2) State :=
  fun schedule =>
    if schedule 0 = 0 then process.leftThenRight
    else process.rightThenLeft

@[simp] theorem scheduleSemantics_refl (process : BinaryProcess State) :
    process.scheduleSemantics (Equiv.refl (Fin 2)) =
      process.leftThenRight := by
  simp [scheduleSemantics]

@[simp] theorem scheduleSemantics_swap (process : BinaryProcess State) :
    process.scheduleSemantics (Equiv.swap (0 : Fin 2) 1) =
      process.rightThenLeft := by
  simp [scheduleSemantics]

/-- Binary schedule invariance is exactly local commutation at the declared
initial state. -/
theorem isChain_iff (process : BinaryProcess State) :
    IsChain process.scheduleSemantics ↔
      process.leftThenRight = process.rightThenLeft := by
  constructor
  · intro chain
    simpa using chain (Equiv.refl (Fin 2)) (Equiv.swap 0 1)
  · intro commute first second
    by_cases firstLeft : first 0 = 0 <;>
      by_cases secondLeft : second 0 = 0 <;>
      simp [scheduleSemantics, firstLeft, secondLeft, commute]

/-- Binary order sensitivity is exactly failure of local commutation. -/
theorem isCoordination_iff (process : BinaryProcess State) :
    IsCoordination process.scheduleSemantics ↔
      process.leftThenRight ≠ process.rightThenLeft := by
  constructor
  · intro coordination equal
    exact (isChain_iff process).mpr equal |>.not_coordination coordination
  · intro different
    exact ⟨Equiv.refl (Fin 2), Equiv.swap 0 1, by simpa using different⟩

/-- A globally commuting pair is a chain from every initial state. -/
theorem isChain_of_commute (initial : State) {left right : State → State}
    (commute : Function.Commute left right) :
    IsChain (BinaryProcess.scheduleSemantics
      ⟨initial, left, right⟩) := by
  rw [isChain_iff]
  exact (commute initial).symm

/-! ## Certified separation -/

/-- Component-local transformations on a product state. -/
def separated {Left : Type uLeft} {Right : Type uRight}
    (initial : Left × Right) (updateLeft : Left → Left)
    (updateRight : Right → Right) : BinaryProcess (Left × Right) where
  initial := initial
  left state := (updateLeft state.1, state.2)
  right state := (state.1, updateRight state.2)

/-- Separated transformations commute as functions, independently of their
particular component behavior. -/
theorem separated_commute {Left : Type uLeft} {Right : Type uRight}
    (updateLeft : Left → Left) (updateRight : Right → Right) :
    Function.Commute
      (fun state : Left × Right => (updateLeft state.1, state.2))
      (fun state : Left × Right => (state.1, updateRight state.2)) := by
  intro state
  rfl

/-- Certified component separation therefore gives a chain. -/
theorem separated_isChain {Left : Type uLeft} {Right : Type uRight}
    (initial : Left × Right) (updateLeft : Left → Left)
    (updateRight : Right → Right) :
    IsChain (separated initial updateLeft updateRight).scheduleSemantics := by
  exact isChain_of_commute initial
    (separated_commute updateLeft updateRight)

/-! ## The induced hierarchical action -/

/-- Two child actions with a schedule-invariant process form a chain action. -/
def chainAction {Outcome : Type uOutcome}
    (process : BinaryProcess Outcome)
    (invariant : IsChain process.scheduleSemantics)
    (child : Fin 2 → Action.{0, uOutcome} Outcome) :
    Action.{0, uOutcome} Outcome :=
  .compound (Fin 2) LimitCanary.binary_hasAtLeastTwo child
    (.chain process.scheduleSemantics invariant)

/-- Two child actions with an order-sensitive process form a coordination
action. -/
def coordinationAction {Outcome : Type uOutcome}
    (process : BinaryProcess Outcome)
    (sensitive : IsCoordination process.scheduleSemantics)
    (child : Fin 2 → Action.{0, uOutcome} Outcome) :
    Action.{0, uOutcome} Outcome :=
  .compound (Fin 2) LimitCanary.binary_hasAtLeastTwo child
    (.coordination process.scheduleSemantics sensitive)

/-- The supremum of a nonempty homogeneous child family is its common rank. -/
theorem childSup_eq_of_equalRank
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    [Nonempty Occurrence]
    (child : Occurrence → Action.{uOccurrence, uOutcome} Outcome)
    (reference : Occurrence)
    (equalRank : ∀ occurrence,
      Action.rank (child occurrence) = Action.rank (child reference)) :
    (⨆ occurrence, Action.rank (child occurrence)) =
      Action.rank (child reference) := by
  apply le_antisymm
  · exact Ordinal.iSup_le fun occurrence => (equalRank occurrence).le
  · exact Ordinal.le_iSup (fun occurrence => Action.rank (child occurrence)) reference

/-- A homogeneous chain preserves the common hierarchical rank. -/
theorem rank_chainAction_of_equalRank
    {Outcome : Type uOutcome}
    (process : BinaryProcess Outcome)
    (invariant : IsChain process.scheduleSemantics)
    (child : Fin 2 → Action.{0, uOutcome} Outcome)
    (equalRank : ∀ occurrence,
      Action.rank (child occurrence) = Action.rank (child 0)) :
    Action.rank (chainAction process invariant child) =
      Action.rank (child 0) := by
  rw [chainAction, Action.rank_chain]
  exact childSup_eq_of_equalRank child (0 : Fin 2) equalRank

/-- A homogeneous coordination raises the common hierarchical rank by one. -/
theorem rank_coordinationAction_of_equalRank
    {Outcome : Type uOutcome}
    (process : BinaryProcess Outcome)
    (sensitive : IsCoordination process.scheduleSemantics)
    (child : Fin 2 → Action.{0, uOutcome} Outcome)
    (equalRank : ∀ occurrence,
      Action.rank (child occurrence) = Action.rank (child 0)) :
    Action.rank (coordinationAction process sensitive child) =
      Order.succ (Action.rank (child 0)) := by
  rw [coordinationAction, Action.rank_coordination]
  congr 1
  exact childSup_eq_of_equalRank child (0 : Fin 2) equalRank

end BinaryProcess

/-! ## An interacting, noncommuting control -/

namespace InteractionCanary

/-- Increment and doubling share one state and do not commute from `1`. -/
def process : BinaryProcess Nat where
  initial := 1
  left number := number + 1
  right number := 2 * number

@[simp] theorem leftThenRight : process.leftThenRight = 4 := by
  rfl

@[simp] theorem rightThenLeft : process.rightThenLeft = 3 := by
  rfl

theorem process_isCoordination :
    IsCoordination process.scheduleSemantics := by
  rw [BinaryProcess.isCoordination_iff]
  decide

/-- The same two simple children remain at order zero under separated
composition. -/
def separatedAction : Action.{0, 0} (Nat × Nat) :=
  BinaryProcess.chainAction
    (BinaryProcess.separated (1, 1) (fun n => n + 1) (fun n => 2 * n))
    (BinaryProcess.separated_isChain
      (1, 1) (fun n => n + 1) (fun n => 2 * n))
    (fun _ => .simple)

theorem rank_separatedAction : Action.rank separatedAction = 0 := by
  exact BinaryProcess.rank_chainAction_of_equalRank _ _ _ (fun _ => rfl)

/-- Sharing state makes the noncommuting version a genuine order-one
coordination. -/
def interactingAction : Action.{0, 0} Nat :=
  BinaryProcess.coordinationAction process process_isCoordination
    (fun _ => .simple)

theorem rank_interactingAction : Action.rank interactingAction = 1 := by
  have rankSuccessor := BinaryProcess.rank_coordinationAction_of_equalRank
    process process_isCoordination (fun _ => .simple) (fun _ => rfl)
  simpa only [interactingAction, Action.rank_simple,
    Order.succ_eq_add_one, zero_add] using rankSuccessor

end InteractionCanary

end Mettapedia.Cybernetics.HierarchicalComplexity.Composition

#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Composition.BinaryProcess.isChain_iff
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Composition.BinaryProcess.isCoordination_iff
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Composition.InteractionCanary.rank_interactingAction
