import Mettapedia.Logic.ProofSearch.Planning
import Mettapedia.GSLT.Core.InferenceControl

/-!
# Controlled proof search with retained evidence and exact expansion cost

The existing occurrence-preserving controller supplies the operational
relation. An emitted answer is an actual solution of the indexed goal.
The first-answer observer retains that object; silent live search stays open,
and completion without an answer exhausts only the authored search space.

The expansion counter records genuine live GSLT steps, not requested fuel
or emitted answers. Costs decorate those same steps. The operational
projection forgets the counter, not the frontier, memory, or proof history.
This is a mathematical adapter, not a correspondence theorem for C.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch.ControlledSearch

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.Core.BranchingTemporal

open Mettapedia.GSLT.Core

universe u v

/-- Exact resumable control state, together with the count of live expansions. -/
structure State (Node Proof Memory : Type u) where
  snapshot : InferenceControl.Snapshot Node Proof Memory
  expanded : Nat

variable {Node Proof Memory : Type u}

/-- The clock decorates the existing control GSLT; it authorizes no new step. -/
def Step (system : BranchingSystem Node Proof)
    (controller : InferenceControl.Controller Node Proof Memory)
    (source target : State Node Proof Memory) : Type u :=
  ULift.{u} (PLift ((InferenceControl.Snapshot.toGSLT system controller).Step
    source.snapshot target.snapshot ∧ target.expanded = source.expanded + 1))

variable {Goal : Type u} {Solution : Goal → Type u}
variable (counter : CounterSystem Goal Solution) (Constraint : Goal → Type u)
variable (goal : Goal)

/-- First-answer readout. Neither silent work nor finite failure is refutation. -/
def observe (state : State Node (Solution goal) Memory) :
    Option (Outcome Solution counter Constraint goal) :=
  match state.snapshot.search.events with
  | event :: _ => some (.solved event.value)
  | [] =>
      match state.snapshot.search.frontier with
      | [] => some (.exhausted (.searchSpace state.expanded))
      | _ :: _ => none

/-- The controller, inference provider, and indexed proof family meet in one
plan. The constraint type is not populated from arbitrary queued work. -/
def plan (system : BranchingSystem Node (Solution goal))
    (controller : InferenceControl.Controller Node (Solution goal) Memory) (roots : List Node) :
    System Solution counter Constraint goal where
  State := State Node (Solution goal) Memory
  initial := ⟨InferenceControl.Snapshot.initial controller roots, 0⟩
  Step := Step system controller
  observe := observe counter Constraint goal

variable {counter Constraint goal}
variable {system : BranchingSystem Node (Solution goal)}
variable {controller : InferenceControl.Controller Node (Solution goal) Memory}
variable {roots : List Node}

theorem observe_none_iff (state : State Node (Solution goal) Memory) :
    observe counter Constraint goal state = none ↔
      state.snapshot.search.events = [] ∧ state.snapshot.search.frontier ≠ [] := by
  cases events : state.snapshot.search.events with
  | nil =>
      cases frontier : state.snapshot.search.frontier <;>
        simp [observe, events, frontier]
  | cons event rest => simp [observe, events]

/-- No score, empty result, or budget stop can manufacture a counter-certificate. -/
theorem observe_ne_refuted (state : State Node (Solution goal) Memory)
    (certificate : counter.Certificate goal)
    (accepted : counter.check certificate = true) :
    observe counter Constraint goal state ≠ some (.refuted certificate accepted) := by
  cases events : state.snapshot.search.events with
  | nil =>
      cases frontier : state.snapshot.search.frontier <;>
        simp [observe, events, frontier]
  | cons event rest => simp [observe, events]

/-- An explicitly bounded observation retains the unmodified resumable state.
The bound changes readout, not the control GSLT or inference relation. -/
def boundedObserve (limit : Nat) (state : State Node (Solution goal) Memory) :
    Option (Outcome Solution counter Constraint goal) :=
  match observe counter Constraint goal state with
  | some outcome => some outcome
  | none =>
      if reached : limit ≤ state.expanded then
        some (.exhausted (.budget limit state.expanded reached))
      else none

theorem bounded_live_exhaustion (limit : Nat)
    (state : State Node (Solution goal) Memory)
    (silent : state.snapshot.search.events = [])
    (live : state.snapshot.search.frontier ≠ [])
    (reached : limit ≤ state.expanded) :
    boundedObserve (counter := counter) (Constraint := Constraint) limit state =
      some (.exhausted (.budget limit state.expanded reached)) := by
  rw [boundedObserve, (observe_none_iff state).mpr ⟨silent, live⟩]
  simp [reached]

/-- A pause exposes genuine constraints only when an interpretation of live
work as those constraints is supplied. The entire snapshot remains resumable. -/
def pause (constraint : Node → Constraint goal)
    (state : State Node (Solution goal) Memory) :
    Option (Residual (Constraint goal) × State Node (Solution goal) Memory) :=
  match state.snapshot.search.frontier with
  | [] => none
  | node :: pending => some (⟨constraint node, pending.map constraint⟩, state)

theorem pause_constraints (constraint : Node → Constraint goal)
    (state : State Node (Solution goal) Memory)
    (residual : Residual (Constraint goal))
    (retained : State Node (Solution goal) Memory)
    (paused : pause constraint state = some (residual, retained)) :
    residual.toList = state.snapshot.search.frontier.map constraint ∧ retained = state := by
  cases frontier : state.snapshot.search.frontier with
  | nil => simp [pause, frontier] at paused
  | cons node pending =>
      simp only [pause, frontier, Option.some.injEq, Prod.mk.injEq] at paused
      rcases paused with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

namespace Trace

/-- Every plan edge projects to the actual existing control step. -/
def project {source target : State Node (Solution goal) Memory} :
    (plan counter Constraint goal system controller roots).Trace source target →
      ExecutionPath (InferenceControl.Snapshot.toGSLT system controller)
        source.snapshot target.snapshot
  | .nil _ => .refl _
  | .cons edge rest => .cons ⟨edge.down.down.1⟩ (project rest)

@[simp] theorem project_append :
    {first middle last : State Node (Solution goal) Memory} →
    (earlier : (plan counter Constraint goal system controller roots).Trace first middle) →
    (later : (plan counter Constraint goal system controller roots).Trace middle last) →
    project (earlier.append later) = (project earlier).append (project later)
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons edge rest, later => by
      simp [project, System.Trace.append, Route.append, project_append rest later]

/-- The counter records the actual projected path, including silent live loops. -/
theorem expanded_eq : {source target : State Node (Solution goal) Memory} →
    (trace : (plan counter Constraint goal system controller roots).Trace source target) →
    target.expanded = source.expanded + (project trace).length
  | _, _, .nil _ => by simp [project, Route.length]
  | _, _, .cons edge rest => by
      have inductionHypothesis := expanded_eq rest
      have increment := edge.down.down.2
      rw [inductionHypothesis, increment]
      simp [project, Route.length]
      omega

/-- Every retained event still comes from an authorized provider occurrence. -/
theorem sound : {source target : State Node (Solution goal) Memory} →
    (trace : (plan counter Constraint goal system controller roots).Trace source target) →
    source.snapshot.search.Sound system roots → target.snapshot.search.Sound system roots
  | _, _, .nil _, sourceSound => sourceSound
  | first, middle, .cons edge rest, sourceSound => by
      apply sound rest
      have targetEq : _ =
          InferenceControl.Snapshot.tick system controller first.snapshot := edge.down.down.1.2
      rw [targetEq]
      exact InferenceControl.Snapshot.sound_tick system controller sourceSound

end Trace

/-- A resource interpretation charges the provider occurrence actually selected.
The no-selection branch is unreachable on a genuine plan step. -/
def costModel {Grade : Type v} [AddMonoid Grade] (charge : Node → Grade) :
    System.CostModel (plan counter Constraint goal system controller roots) Grade where
  charge := fun {source _target} _edge =>
    match InferenceControl.Snapshot.selected controller source.snapshot with
    | none => 0
    | some node => charge node

def expansionCost :
    System.CostModel (plan counter Constraint goal system controller roots) Nat where
  charge _ := 1

theorem expansion_cost_eq_path_length : {source target : State Node (Solution goal) Memory} →
    (trace : (plan counter Constraint goal system controller roots).Trace source target) →
    expansionCost.total trace = (Trace.project trace).length
  | _, _, .nil _ => rfl
  | _, _, .cons edge rest => by
      change 1 + expansionCost.total rest = (Trace.project rest).length + 1
      rw [expansion_cost_eq_path_length rest, Nat.add_comm]

/-- Empty-frontier completion has no billable outgoing step. -/
theorem no_step_of_complete (state : State Node (Solution goal) Memory)
    (complete : state.snapshot.search.frontier = []) :
    ¬ ∃ target, Nonempty (Step system controller state target) := by
  rintro ⟨target, ⟨edge⟩⟩
  exact edge.down.down.1.1 complete

/-- Count only genuine live expansions in the existing run. Completed
frontiers consume no further work, even if more fuel was requested. -/
def expansions (system : BranchingSystem Node Proof)
    (controller : InferenceControl.Controller Node Proof Memory)
    (source : InferenceControl.Snapshot Node Proof Memory) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
      if (InferenceControl.Snapshot.run system controller fuel source).search.frontier = [] then
        expansions system controller source fuel
      else expansions system controller source fuel + 1

theorem expansions_eq_fuel (fuel : Nat)
    (source : InferenceControl.Snapshot Node (Solution goal) Memory)
    (live : InferenceControl.Snapshot.LiveThrough system controller fuel source) :
    expansions system controller source fuel = fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      have livePrefix : InferenceControl.Snapshot.LiveThrough system controller fuel source :=
        fun elapsed less => live elapsed (Nat.lt_trans less (Nat.lt_succ_self fuel))
      simp only [expansions, if_neg (live fuel (Nat.lt_succ_self fuel)),
        inductionHypothesis livePrefix]

theorem expansions_le_fuel (fuel : Nat)
    (source : InferenceControl.Snapshot Node (Solution goal) Memory) :
    expansions system controller source fuel ≤ fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [expansions]
      split <;> omega

/-- Resumption accounts for exactly the work performed in both chunks. -/
theorem expansions_add (left right : Nat)
    (source : InferenceControl.Snapshot Node (Solution goal) Memory) :
    expansions system controller source (left + right) =
      expansions system controller source left +
        expansions system controller (InferenceControl.Snapshot.run system controller left source)
          right := by
  induction right with
  | zero => simp [expansions]
  | succ right inductionHypothesis =>
      simp only [Nat.add_succ, expansions]
      have routeEquation : InferenceControl.Snapshot.run system controller (left.add right) source =
          InferenceControl.Snapshot.run system controller right
            (InferenceControl.Snapshot.run system controller left source) :=
        InferenceControl.Snapshot.run_add system controller left right source
      have countEquation : expansions system controller source (left.add right) =
          expansions system controller source left +
            expansions system controller (InferenceControl.Snapshot.run system controller left source)
              right := inductionHypothesis
      rw [routeEquation, countEquation]
      split <;> simp [Nat.add_assoc]

/-- The actual controlled snapshot with a saturating expansion clock. -/
def runState (system : BranchingSystem Node (Solution goal))
    (controller : InferenceControl.Controller Node (Solution goal) Memory)
    (fuel : Nat) (source : State Node (Solution goal) Memory) :
    State Node (Solution goal) Memory :=
  ⟨InferenceControl.Snapshot.run system controller fuel source.snapshot,
    source.expanded + expansions system controller source.snapshot fuel⟩

theorem runState_add (left right : Nat) (source : State Node (Solution goal) Memory) :
    runState system controller (left + right) source =
      runState system controller right (runState system controller left source) := by
  simp [runState, InferenceControl.Snapshot.run_add, expansions_add, Nat.add_assoc]

/-- Every fuel prefix has an actual trace. Terminal stutters add neither
an edge nor a cost; liveness is needed only to equate cost with all fuel. -/
def boundedRunTrace (fuel : Nat) (source : State Node (Solution goal) Memory) :
    (plan counter Constraint goal system controller roots).Trace source
      (runState system controller fuel source) := by
  induction fuel with
  | zero => exact .nil _
  | succ fuel inductionHypothesis =>
      by_cases complete :
          (InferenceControl.Snapshot.run system controller fuel source.snapshot).search.frontier = []
      · have same : runState system controller (fuel + 1) source =
            runState system controller fuel source := by
          simp [runState, InferenceControl.Snapshot.run, expansions, complete,
            InferenceControl.Snapshot.tick_eq_self_of_frontier_nil
              system controller _ complete]
        rw [same]
        exact inductionHypothesis
      · refine inductionHypothesis.append (.cons ?_ (.nil _))
        exact ⟨⟨⟨⟨complete, rfl⟩,
          by simp [runState, expansions, complete, Nat.add_assoc]⟩⟩⟩

theorem bounded_run_cost (fuel : Nat) (source : State Node (Solution goal) Memory) :
    expansionCost.total (boundedRunTrace (counter := counter) (Constraint := Constraint)
      (system := system) (controller := controller)
      (roots := roots) fuel source) = expansions system controller source.snapshot fuel := by
  have clock := Trace.expanded_eq (boundedRunTrace (counter := counter)
    (Constraint := Constraint) (system := system) (controller := controller)
    (roots := roots) fuel source)
  rw [expansion_cost_eq_path_length]
  change source.expanded + expansions system controller source.snapshot fuel =
    source.expanded + _ at clock
  exact Nat.add_left_cancel clock.symm

def runTrace (fuel : Nat) (source : State Node (Solution goal) Memory)
    (live : InferenceControl.Snapshot.LiveThrough system controller fuel source.snapshot) :
    (plan counter Constraint goal system controller roots).Trace source
      (runState system controller fuel source) := by
  induction fuel with
  | zero => exact .nil _
  | succ fuel inductionHypothesis =>
      have livePrefix : InferenceControl.Snapshot.LiveThrough system controller fuel source.snapshot :=
        fun elapsed less => live elapsed (Nat.lt_trans less (Nat.lt_succ_self fuel))
      refine (inductionHypothesis livePrefix).append (.cons ?_ (.nil _))
      exact ⟨⟨⟨⟨live fuel (Nat.lt_succ_self fuel), rfl⟩,
        by simp [runState, expansions, live fuel (Nat.lt_succ_self fuel), Nat.add_assoc]⟩⟩⟩

theorem run_expansion_cost (fuel : Nat) (source : State Node (Solution goal) Memory)
    (live : InferenceControl.Snapshot.LiveThrough system controller fuel source.snapshot) :
    expansionCost.total (runTrace (counter := counter) (Constraint := Constraint)
      (roots := roots) fuel source live) = fuel := by
  have clock := Trace.expanded_eq (runTrace (counter := counter) (Constraint := Constraint)
    (roots := roots) fuel source live)
  rw [expansion_cost_eq_path_length]
  change source.expanded + expansions system controller source.snapshot fuel =
    source.expanded + _ at clock
  rw [expansions_eq_fuel fuel source.snapshot live] at clock
  exact Nat.add_left_cancel clock.symm

/-- Already completed search preserves both the snapshot and its clock. -/
theorem runState_of_complete (fuel : Nat) (source : State Node (Solution goal) Memory)
    (complete : source.snapshot.search.frontier = []) :
    runState system controller fuel source = source := by
  have noExpansions : expansions system controller source.snapshot fuel = 0 := by
    induction fuel with
    | zero => rfl
    | succ fuel inductionHypothesis =>
        simp [expansions, InferenceControl.Snapshot.run_eq_self_of_frontier_nil
          system controller source.snapshot complete, inductionHypothesis, complete]
  simp [runState, InferenceControl.Snapshot.run_eq_self_of_frontier_nil
    system controller source.snapshot complete, noExpansions]

/-- Actual root-to-state traces justify the origin of a first retained proof. -/
theorem solved_has_origin {proof : Solution goal}
    {state : State Node (Solution goal) Memory}
    (trace : (plan counter Constraint goal system controller roots).Trace
      (plan counter Constraint goal system controller roots).initial state)
    (solved : observe counter Constraint goal state = some (.solved proof)) :
    ∃ node, Generated system roots node ∧ system.emit node = some proof := by
  have stateSound := Trace.sound trace (initial_sound system roots)
  cases events : state.snapshot.search.events with
  | nil =>
      cases frontier : state.snapshot.search.frontier <;>
        simp [observe, events, frontier] at solved
  | cons event pending =>
      have same : event.value = proof := by simpa [observe, events] using solved
      obtain ⟨generated, emitted⟩ := stateSound.2 event (by simp [events])
      exact ⟨event.origin, generated, by simpa [same] using emitted⟩

#print axioms Trace.expanded_eq
#print axioms Trace.sound
#print axioms Trace.project_append
#print axioms expansion_cost_eq_path_length
#print axioms run_expansion_cost
#print axioms runState_of_complete
#print axioms bounded_run_cost
#print axioms runState_add
#print axioms solved_has_origin
#print axioms observe_ne_refuted
#print axioms pause_constraints

end Mettapedia.Logic.ProofSearch.ControlledSearch
