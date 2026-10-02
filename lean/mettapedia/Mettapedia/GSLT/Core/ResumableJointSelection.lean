import Mettapedia.GSLT.Core.JointDemand
import Mettapedia.GSLT.Core.WellFoundedSearch
import Mettapedia.GSLT.Core.WeightOrderedSelection

/-!
# Resumable include/exclude search for joint witnesses

Pending work contains an unexamined suffix, the partial collection and its
remaining demand. Each expansion inspects one occurrence and retains both the
include and exclude alternatives. The executor is the existing controlled
worklist, not an eagerly enumerated list of complete collections.

The source observation is independently specified by `List.sublistsLen`.
Structural descent proves closure, and the denotation theorem proves exact
collection multiplicity for every lawful controller.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ResumableJointSelection

open BranchingTemporal

variable {Answer Memory : Type*}

structure Work (Answer : Type*) where
  remaining : List Answer
  chosen : List Answer
  needed : Nat
  deriving DecidableEq, Repr

def system (goal : List Answer → Bool) : BranchingSystem (Work Answer) (List Answer) where
  emit state := if state.needed = 0 && goal state.chosen then some state.chosen else none
  successors state := match state.needed, state.remaining with
    | 0, _ => []
    | _ + 1, [] => []
    | count + 1, answer :: remaining =>
        [⟨remaining, state.chosen, count + 1⟩,
         ⟨remaining, state.chosen ++ [answer], count⟩]

def depth (goal : List Answer → Bool) : WellFoundedSearch.DepthBound (system goal) where
  depth state := state.remaining.length
  decreases state child member := by
    rcases state with ⟨remaining, chosen, needed⟩
    cases needed with
    | zero => simp [system] at member
    | succ needed =>
        cases remaining with
        | nil => simp [system] at member
        | cons answer remaining =>
            simp only [system, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with same | same <;> subst child <;> simp

def observation (goal : List Answer → Bool) (state : Work Answer) : List (List Answer) :=
  ((List.sublistsLen state.needed state.remaining).map (state.chosen ++ ·)).filter goal

/-- Exact occurrence semantics is derived from include/exclude transitions.
It is not an unfolding law assumed as a native correctness premise. -/
theorem denotation_exact (goal : List Answer → Bool) (state : Work Answer) :
    (WellFoundedSearch.denotation (system goal) (depth goal)).value state =
      (observation goal state : Multiset (List Answer)) := by
  rcases state with ⟨remaining, chosen, needed⟩
  induction remaining generalizing chosen needed with
  | nil =>
      rw [(WellFoundedSearch.denotation (system goal) (depth goal)).unfold]
      cases needed with
      | zero =>
          cases accepted : goal chosen <;>
            simp [system, observation, List.sublistsLen_zero, accepted, optionBag, foldValues]
      | succ needed =>
          simp [system, observation, List.sublistsLen_succ_nil, optionBag, foldValues]
  | cons answer remaining ih =>
      rw [(WellFoundedSearch.denotation (system goal) (depth goal)).unfold]
      cases needed with
      | zero =>
          cases accepted : goal chosen <;>
            simp [system, observation, List.sublistsLen_zero, accepted, optionBag, foldValues]
      | succ needed =>
          rw [show (system goal).emit ⟨answer :: remaining, chosen, needed + 1⟩ = none by
            simp [system]]
          rw [show (system goal).successors ⟨answer :: remaining, chosen, needed + 1⟩ =
            [⟨remaining, chosen, needed + 1⟩,
             ⟨remaining, chosen ++ [answer], needed⟩] by rfl]
          simp only [optionBag, foldValues, add_zero, zero_add]
          rw [ih chosen (needed + 1), ih (chosen ++ [answer]) needed]
          simp [observation, List.sublistsLen_succ_cons, List.map_map,
            Function.comp_def, List.append_assoc]

def initial (requested : Nat) (seen : List Answer) : Work Answer := ⟨seen, [], requested⟩

/-- Recompute a branch's priority from its current partial collection. Including
an occurrence can change every later marginal preference; excluded siblings
remain authorized work. Smaller scores receive earlier expansion. -/
def adaptiveController (score : List Answer → Nat) :
    InferenceControl.Controller (Work Answer) (List Answer) Unit :=
  let rank := fun (first second : Work Answer) => score first.chosen ≤ score second.chosen
  letI : DecidableRel rank := fun _ _ => inferInstance
  letI : IsTrans (Work Answer) rank := ⟨fun _ _ _ first second => le_trans first second⟩
  letI : Std.Total rank :=
    ⟨fun first second => le_total (score first.chosen) (score second.chosen)⟩
  InferenceControl.Controller.fixed (WeightOrderedSelection.orderScheduler rank)

theorem adaptive_order_preserves (score : List Answer → Nat) (frontier : List (Work Answer)) :
    (((adaptiveController score).scheduler ()).reorder frontier).Perm frontier :=
  ((adaptiveController score).scheduler ()).reorder_complete frontier

theorem initial_observation (goal : List Answer → Bool) (requested : Nat)
    (seen : List Answer) :
    observation goal (initial requested seen) = JointDemand.candidates goal requested seen := by
  simp [observation, initial, JointDemand.candidates]

/-- Every occurrence-preserving controller exhausts the constructed finite
collection search and returns exactly the independently specified witnesses. -/
theorem complete_correct (goal : List Answer → Bool) (requested : Nat) (seen : List Answer)
    (controller : InferenceControl.Controller (Work Answer) (List Answer) Memory) :
    let roots := [initial requested seen]
    let budget := foldRanks (WellFoundedSearch.descent (system goal) (depth goal)).rank roots
    let result := InferenceControl.Snapshot.run (system goal) controller budget
      (InferenceControl.Snapshot.initial controller roots)
    result.search.frontier = [] ∧ eventBag result.search.events =
      (JointDemand.candidates goal requested seen : Multiset (List Answer)) := by
  intro roots budget result
  have closed := WellFoundedSearch.completes (system goal) (depth goal) controller roots
  refine ⟨closed, ?_⟩
  have exactBag := InferenceControl.Snapshot.completed_run_denotation
    (system goal) controller (WellFoundedSearch.denotation (system goal) (depth goal))
    roots budget closed
  simpa [roots, foldValues, denotation_exact, initial_observation] using exactBag

/-- Adaptive partial-collection guidance changes expansion order while the
constructed finite search still exhausts all independently specified witnesses.
No monotonicity or correctness assumption about the heuristic is needed. -/
theorem adaptive_complete (goal : List Answer → Bool) (score : List Answer → Nat)
    (requested : Nat) (seen : List Answer) :
    let roots := [initial requested seen]
    let budget := foldRanks (WellFoundedSearch.descent (system goal) (depth goal)).rank roots
    let result := InferenceControl.Snapshot.run (system goal) (adaptiveController score) budget
      (InferenceControl.Snapshot.initial (adaptiveController score) roots)
    result.search.frontier = [] ∧ eventBag result.search.events =
      (JointDemand.candidates goal requested seen : Multiset (List Answer)) :=
  complete_correct goal requested seen (adaptiveController score)

def run (goal : List Answer → Bool)
    (controller : InferenceControl.Controller (Work Answer) (List Answer) Memory)
    (fuel : Nat) (state : DemandExecution.State (Work Answer) (List Answer) Memory) :
    DemandExecution.State (Work Answer) (List Answer) Memory :=
  DemandExecution.run (system goal) controller (DemandExecution.atLeast 1) fuel state

theorem pause_resume (goal : List Answer → Bool)
    (controller : InferenceControl.Controller (Work Answer) (List Answer) Memory)
    (first second : Nat) (state : DemandExecution.State (Work Answer) (List Answer) Memory) :
    run goal controller (first + second) state =
      run goal controller second (run goal controller first state) :=
  DemandExecution.run_add (system goal) controller (DemandExecution.atLeast 1)
    first second state

namespace Controls

def distinctPair (values : List Nat) : Bool := decide (values = [1, 2])

example : observation distinctPair (initial 2 [1, 1, 2]) = [[1, 2], [1, 2]] := by decide
example : (system distinctPair).successors (initial 2 [1, 1, 2]) ≠ [] := by decide
example : (system distinctPair).emit (initial 2 [1, 1, 2]) = none := by decide

/-- One rejected partial collection does not close its sibling alternative. -/
example : observation distinctPair ⟨[2], [1, 1], 0⟩ = [] ∧
    observation distinctPair ⟨[2], [1], 1⟩ = [[1, 2]] := by decide

end Controls

end Mettapedia.GSLT.Core.ResumableJointSelection
