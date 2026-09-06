import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachine

/-!
# Actual scoped Need-machine execution controls

The observations below run the existing owned Need machine. They retain
halted outcome status and chronological effect receipts. They do not identify
source choice traces with full protocol paths, which also retain administrative
singleton forks, allocation, ownership, and observation events.

Native answers are raw presentation terms. Failure controls retain stable
versus retryable status, while unfinished fuel retains a live frontier rather
than furnishing a negative logical result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedMachineExamples

open PrimeNeedReference ScopedNeedComputation ScopedNeedMachine

inductive Operation where
  | identity
  | stable
  | retry
  deriving DecidableEq, Repr

abbrev Source := Code Nat Operation Nat 0 0
abbrev ExampleMachine := NeedMachine Nat Operation Nat Nat Nat 0

def primitive : Operation → Tm Nat 0 → Produced (Tm Nat 0) Nat Nat
  | .identity, argument => .value argument
  | .stable, _ => .stableFault 11
  | .retry, _ => .retryableFault (.domain 13)

def machineSpec : NeedSpec Nat Operation Nat Nat Nat 0 := spec primitive

def initial (source : Source) : ExampleMachine where
  world :=
    { lineage := 0, path := [], heap := .empty, receipts := .empty,
      nextCell := 0, nextEvaluator := 0 }
  control := .run (.evaluate ⟨0, 0, source, ids, Fin.elim0⟩ .done) []

def frontier (fuel : Nat) (source : Source) : List ExampleMachine :=
  runFrontier machineSpec fuel [initial source]

/-- Read only actual effect events, in causal execution order. The full
machine and its other receipts remain available in the frontier. -/
def effects (machine : ExampleMachine) : List Nat :=
  machine.world.receipts.nodes.reverse.filterMap fun node =>
    match node.payload with
    | .effect effect => some effect
    | _ => none

def observe (machine : ExampleMachine) :
    Option (Outcome Nat Nat Nat 0) × List Nat :=
  (haltedOutcome machine, effects machine)

def observations (fuel : Nat) (source : Source) := (frontier fuel source).map observe

/-- Effect emission belongs to the suspended producer, before its choice. -/
def producer {n k : Nat} : Code Nat Operation Nat n k :=
  .emit 7 (.choose (.returnValue (.head 10)) (.returnValue (.head 20)))

def unused : Source := .letNeed producer (.returnValue (.head 99))

/-- Both force sites resolve the same suspension reference. -/
def shared : Source :=
  .letNeed producer (.sequenceSigma (.force 0) (.force 0))

/-- The producers have equal syntax but different dynamic cell identities. -/
def independent : Source :=
  .letNeed producer (.letNeed producer (.sequenceSigma (.force 1) (.force 0)))

def stableFailure : Source :=
  .sequenceSigma (.emit 3 (.call .stable (.head 0)))
    (.emit 4 (.returnValue (.var 0)))

def retryFailure : Source :=
  .sequenceSigma (.emit 3 (.call .retry (.head 0)))
    (.emit 4 (.returnValue (.var 0)))

def firstCell : CellId := ⟨0, [], 0, 0⟩

inductive CacheTag where
  | suspended
  | evaluating
  | value
  | stableFault
  deriving DecidableEq, Repr

def cacheTag (machine : ExampleMachine) (cell : CellId) : Option CacheTag :=
  (machine.world.heap.lookup cell).map fun record =>
    match record.cache with
    | .suspended => .suspended
    | .evaluating _ => .evaluating
    | .value _ => .value
    | .stableFault _ => .stableFault

/-- Retry from the actual resulting world; no prior receipts are discarded. -/
def forceAgain (machine : ExampleMachine) : ExampleMachine :=
  { machine with control := .force firstCell [] }

def retried : List ExampleMachine :=
  runFrontier machineSpec 32 ((frontier 32 retryFailure).map forceAgain)

/-- Suspending an effectful producer does not execute its effect. -/
theorem unused_suspension_emits_nothing :
    observations 64 unused = [(some (.value (.head 99)), [])] := by
  rfl

/-- Each branch records exactly one producer effect and a correlated pair.
The second demand returns the selected raw native term from the same cell. -/
theorem shared_force_twice :
    observations 64 shared =
      [(some (.value (.pair (.head 10) (.head 10))), [7]),
       (some (.value (.pair (.head 20) (.head 20))), [7])] := by
  rfl

/-- Independently allocated producers make independent choices, even though
their authored source is the same, and each execution emits its effect. -/
theorem independent_cells_choose_independently :
    observations 64 independent =
      [(some (.value (.pair (.head 10) (.head 10))), [7, 7]),
       (some (.value (.pair (.head 10) (.head 20))), [7, 7]),
       (some (.value (.pair (.head 20) (.head 10))), [7, 7]),
       (some (.value (.pair (.head 20) (.head 20))), [7, 7])] := by
  rfl

/-- The ordinary answer projection is the status-preserving projection of
these observations; it does not filter away failures as though they were false. -/
theorem answers_from_observations (fuel : Nat) (source : Source) :
    answers machineSpec fuel (initial source) =
      (observations fuel source).filterMap Prod.fst := by
  simp only [answers, observations, frontier, List.filterMap_map, observe, Function.comp_def]

theorem shared_answers :
    answers machineSpec 64 (initial shared) =
      [.value (.pair (.head 10) (.head 10)), .value (.pair (.head 20) (.head 20))] := by
  rw [answers_from_observations, shared_force_twice]
  rfl

/-- Shared force cannot silently resample into a mixed pair. -/
theorem shared_has_no_mixed_pair :
    .value (.pair (.head 10) (.head 20)) ∉ answers machineSpec 64 (initial shared) := by
  rw [shared_answers]
  decide

theorem independent_cells_are_not_silently_shared :
    observations 64 independent ≠ observations 64 shared := by
  rw [independent_cells_choose_independently, shared_force_twice]
  decide

theorem stable_fault_stops_continuation :
    observations 32 stableFailure = [(some (.stableFault 11), [3])] := by
  rfl

theorem stable_fault_is_cached :
    (frontier 32 stableFailure).map (fun machine => cacheTag machine firstCell) =
      [some .stableFault] := by
  rfl

theorem retryable_fault_stops_continuation :
    observations 32 retryFailure =
      [(some (.retryableFault (.domain (.native 13))), [3])] := by
  rfl

theorem retryable_fault_restores_suspension :
    (frontier 32 retryFailure).map (fun machine => cacheTag machine firstCell) =
      [some .suspended] := by
  rfl

/-- Retrying does not undo the first execution's effect receipt. The new
attempt emits once more; it still does not enter the marked continuation. -/
theorem retry_does_not_roll_back_prior_effects :
    retried.map observe =
      [(some (.retryableFault (.domain (.native 13))), [3, 3])] := by
  rfl

theorem retry_is_not_effect_rollback :
    retried.map observe ≠ [(some (.retryableFault (.domain (.native 13))), [3])] := by
  rw [retry_does_not_roll_back_prior_effects]
  decide

/-- One step allocates the unused suspension but has not returned yet.
The empty answer list therefore accompanies a retained, non-halted frontier. -/
theorem unfinished_fuel_retains_live_frontier :
    observations 1 unused = [(none, [])] ∧
      (frontier 1 unused).map isHalted = [false] ∧
      answers machineSpec 1 (initial unused) = [] := by
  exact ⟨rfl, rfl, rfl⟩

/-- Giving the same execution enough fuel returns its value; lack of an
early answer is not a refutation of the suspended computation. -/
theorem unfinished_is_not_a_negative_result :
    answers machineSpec 1 (initial unused) = [] ∧
      answers machineSpec 64 (initial unused) = [.value (.head 99)] := by
  constructor
  · rfl
  · rw [answers_from_observations, unused_suspension_emits_nothing]
    rfl

#print axioms unused_suspension_emits_nothing
#print axioms shared_force_twice
#print axioms independent_cells_choose_independently
#print axioms shared_answers
#print axioms shared_has_no_mixed_pair
#print axioms independent_cells_are_not_silently_shared
#print axioms stable_fault_stops_continuation
#print axioms stable_fault_is_cached
#print axioms retryable_fault_stops_continuation
#print axioms retryable_fault_restores_suspension
#print axioms retry_does_not_roll_back_prior_effects
#print axioms retry_is_not_effect_rollback
#print axioms unfinished_fuel_retains_live_frontier
#print axioms unfinished_is_not_a_negative_result

end ScopedNeedMachineExamples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
