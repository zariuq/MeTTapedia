import Mettapedia.GSLT.Core.SearchControlProperties

/-!
# Observer-indexed stream productivity

Lane recurrence, occurrence fairness, finite closure, finite-bag agreement,
and productive output are different claims.  This module adds the missing
productive-output claim without changing any of the others.

An `EventObserver` is a candidate-local partial view of one emitted
occurrence.  A scenario is productive for an expected stream when every
finite requested prefix of that stream appears after finite execution fuel.
The definition is chronological, observer-indexed, and demand-indexed.  It
does not require the frontier to close and does not manufacture a finite bag
meaning for an infinite computation.

The canaries establish all relevant separations:

* a fair silent loop is not productive for a nonempty observed stream;
* a productive depth-first loop may still starve another live occurrence;
* a productive stream need not close or carry a finite additive bag meaning;
* a closed one-answer run is not productive for an infinite two-or-more-answer
  demand;
* recurring selection of a silent occurrence supplies no productive output.
-/

namespace Mettapedia.GSLT.Core.SearchStreamProductivity

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.SearchControlProperties

universe uNode uAnswer uView uMapped

/-! ## Event observers and demanded prefixes -/

/-- A candidate-local observer may expose one view of an emitted occurrence
or hide that occurrence.  Whole-stream normalization and selection are not
fields of this interface. -/
structure EventObserver
    (Node : Type uNode) (Answer : Type uAnswer) (View : Type uView) where
  observe : Emission Node Answer → Option View

namespace EventObserver

variable {Node : Type uNode} {Answer : Type uAnswer} {View : Type uView}
  {Mapped : Type uMapped}

/-- Observe a chronological event prefix without changing its order. -/
def observeList (observer : EventObserver Node Answer View)
    (events : List (Emission Node Answer)) : List View :=
  events.filterMap observer.observe

/-- Observe the answer while retaining occurrence chronology in the source
event list. -/
def value : EventObserver Node Answer Answer where
  observe event := some event.value

/-- Hide every event.  This is useful as a negative observer control. -/
def silent : EventObserver Node Answer View where
  observe _ := none

/-- Reindex an admitted local view. -/
def map (observer : EventObserver Node Answer View) (f : View → Mapped) :
    EventObserver Node Answer Mapped where
  observe event := (observer.observe event).map f

@[simp] theorem observeList_append (observer : EventObserver Node Answer View)
    (earlier later : List (Emission Node Answer)) :
    observer.observeList (earlier ++ later) =
      observer.observeList earlier ++ observer.observeList later := by
  simp [observeList]

/-- Candidate-local observation preserves chronological prefix inclusion. -/
theorem observeList_prefix (observer : EventObserver Node Answer View)
    {earlier later : List (Emission Node Answer)}
    (prefixEvidence : earlier.IsPrefix later) :
    (observer.observeList earlier).IsPrefix (observer.observeList later) := by
  exact prefixEvidence.filterMap observer.observe

@[simp] theorem observeList_value (events : List (Emission Node Answer)) :
    (value : EventObserver Node Answer Answer).observeList events =
      events.map Emission.value := by
  induction events with
  | nil => rfl
  | cons event events inductionHypothesis =>
      simp [observeList, value]

@[simp] theorem observeList_silent (events : List (Emission Node Answer)) :
    (silent : EventObserver Node Answer View).observeList events = [] := by
  induction events <;> simp_all [observeList, silent]

@[simp] theorem observeList_map
    (observer : EventObserver Node Answer View) (f : View → Mapped)
    (events : List (Emission Node Answer)) :
    (observer.map f).observeList events =
      (observer.observeList events).map f := by
  change
    List.filterMap (fun event => (observer.observe event).map f) events =
      (List.filterMap observer.observe events).map f
  exact List.map_filterMap.symm

end EventObserver

/-- The first `demand` values of an authored infinite stream. -/
def streamPrefix {View : Type uView} (expected : Nat → View)
    (demand : Nat) : List View :=
  List.ofFn fun index : Fin demand => expected index.1

@[simp] theorem streamPrefix_zero {View : Type uView} (expected : Nat → View) :
    streamPrefix expected 0 = [] := by
  rfl

@[simp] theorem streamPrefix_const {View : Type uView}
    (view : View) (demand : Nat) :
    streamPrefix (fun _ => view) demand = List.replicate demand view := by
  exact List.ofFn_const demand view

theorem streamPrefix_map {View : Type uView} {Mapped : Type uMapped}
    (expected : Nat → View) (f : View → Mapped) (demand : Nat) :
    (streamPrefix expected demand).map f =
      streamPrefix (fun index => f (expected index)) demand := by
  simp [streamPrefix, Function.comp_def, List.map_ofFn]

/-- A demanded prefix can equivalently be enumerated by its natural indices. -/
theorem streamPrefix_eq_range_map {View : Type uView}
    (expected : Nat → View) (demand : Nat) :
    streamPrefix expected demand = (List.range demand).map expected := by
  simpa [streamPrefix] using
    (List.ofFn_getElem_eq_map (List.range demand) expected)

namespace Scenario

variable {Node : Type uNode} {Answer : Type uAnswer} {View : Type uView}

/-- Every finite prefix requested by an observer is available after finite
fuel.  The witnessing fuel may depend on the demand. -/
def StreamProductiveFor (scenario : Scenario Node Answer)
    (observer : EventObserver Node Answer View)
    (expected : Nat → View) : Prop :=
  ∀ demand, ∃ fuel,
    (streamPrefix expected demand).IsPrefix
      (observer.observeList (scenario.snapshotAt fuel).events)

/-- Resuming a scenario never retracts an already observed prefix. -/
theorem observed_prefix_after_resume (scenario : Scenario Node Answer)
    (observer : EventObserver Node Answer View) (fuel extra : Nat) :
    (observer.observeList (scenario.snapshotAt fuel).events).IsPrefix
      (observer.observeList (scenario.snapshotAt (fuel + extra)).events) := by
  apply observer.observeList_prefix
  change
    (run scenario.system scenario.scheduler fuel
        (initial scenario.roots)).events.IsPrefix
      (run scenario.system scenario.scheduler (fuel + extra)
        (initial scenario.roots)).events
  rw [run_add]
  exact events_prefix_run scenario.system scenario.scheduler extra _

/-- Stream productivity is covariant under a local map of the admitted view. -/
theorem StreamProductiveFor.map
    {scenario : Scenario Node Answer}
    {observer : EventObserver Node Answer View}
    {expected : Nat → View}
    (productive : StreamProductiveFor scenario observer expected)
    (f : View → Mapped) :
    StreamProductiveFor scenario (observer.map f)
      (fun index => f (expected index)) := by
  intro demand
  obtain ⟨fuel, prefixEvidence⟩ := productive demand
  refine ⟨fuel, ?_⟩
  rw [← streamPrefix_map expected f demand,
    EventObserver.observeList_map]
  exact prefixEvidence.map f

end Scenario

/-! ## Separating canaries -/

namespace Canaries

open Scenario
open SearchControlProperties.Canaries

/-! ### A productive fair stream that never closes -/

/-- The exact chronological events produced by the one-node productive loop. -/
theorem productive_events_eq_replicate (answer : Answer) (fuel : Nat) :
    ((productiveScenario answer).snapshotAt fuel).events =
      List.replicate fuel ⟨(), answer⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      change
        (tick (productiveLoopSystem answer) Scheduler.breadthFirst
          (run (productiveLoopSystem answer) Scheduler.breadthFirst fuel
            (initial [()]))).events =
          List.replicate (fuel + 1) ⟨(), answer⟩
      have frontier := productive_frontier_eq_singleton answer fuel
      change
        (run (productiveLoopSystem answer) Scheduler.breadthFirst fuel
          (initial [()])).events =
            List.replicate fuel ⟨(), answer⟩ at inductionHypothesis
      change
        (run (productiveLoopSystem answer) Scheduler.breadthFirst fuel
          (initial [()])).frontier = [()] at frontier
      have ordered :
          Scheduler.breadthFirst.reorder
              (run (productiveLoopSystem answer) Scheduler.breadthFirst fuel
                (initial [()])).frontier = [()] := by
        simpa [Scheduler.breadthFirst] using frontier
      unfold tick
      rw [ordered, inductionHypothesis, List.replicate_succ']
      rfl

/-- Every finite constant-answer demand is met after exactly that much fuel. -/
theorem productive_stream (answer : Answer) :
    StreamProductiveFor (productiveScenario answer) EventObserver.value
      (fun _ => answer) := by
  intro demand
  refine ⟨demand, ?_⟩
  rw [streamPrefix_const, EventObserver.observeList_value,
    productive_events_eq_replicate]
  simp

/-- Stream productivity is compatible with occurrence fairness but does not
imply finite closure or a fabricated finite bag semantics. -/
theorem productive_fair_open_and_not_finite_bag (answer : Answer) :
    StreamProductiveFor (productiveScenario answer) EventObserver.value
        (fun _ => answer) ∧
      (productiveScenario answer).OccurrenceFair ∧
      ¬ (productiveScenario answer).FinitelyCloses ∧
      ¬ Nonempty (DeclaredBagMeaning (productiveScenario answer)) :=
  ⟨productive_stream answer, productive_occurrence_fair answer,
    productive_not_finitely_closes answer,
    productive_has_no_declared_finite_bag_meaning answer⟩

/-! ### Fairness without productive observed output -/

def silentLoopSystem : BranchingSystem Unit Unit where
  emit _ := none
  successors _ := [()]

def silentLoopScenario : Scenario Unit Unit where
  system := silentLoopSystem
  scheduler := Scheduler.breadthFirst
  roots := [()]

theorem silentLoop_run_eq (fuel : Nat) :
    run silentLoopSystem Scheduler.breadthFirst fuel (initial [()]) =
      { events := [], frontier := [()] } := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      change
        tick silentLoopSystem Scheduler.breadthFirst
            (run silentLoopSystem Scheduler.breadthFirst fuel (initial [()])) =
          { events := [], frontier := [()] }
      rw [inductionHypothesis]
      rfl

theorem silentLoop_occurrence_fair : silentLoopScenario.OccurrenceFair :=
  breadthFirst_fair silentLoopSystem [()]

theorem silentLoop_not_stream_productive :
    ¬ StreamProductiveFor silentLoopScenario EventObserver.value
      (fun _ => ()) := by
  intro productive
  obtain ⟨fuel, prefixEvidence⟩ := productive 1
  have noEvents : (silentLoopScenario.snapshotAt fuel).events = [] := by
    exact congrArg Snapshot.events (silentLoop_run_eq fuel)
  rw [EventObserver.observeList_value, noEvents] at prefixEvidence
  simp [streamPrefix] at prefixEvidence

/-- Occurrence fairness does not by itself promise output for an observer. -/
theorem occurrence_fairness_does_not_imply_stream_productivity :
    silentLoopScenario.OccurrenceFair ∧
      ¬ StreamProductiveFor silentLoopScenario EventObserver.value
        (fun _ => ()) :=
  ⟨silentLoop_occurrence_fair, silentLoop_not_stream_productive⟩

/-! ### Productive output while another live occurrence starves -/

namespace ProductiveStarvation

def system : BranchingSystem BranchingTemporal.Starvation.Node Nat where
  emit
    | .loop => some 0
    | .answer => some 42
  successors
    | .loop => [.loop]
    | .answer => []

def scenario : Scenario BranchingTemporal.Starvation.Node Nat where
  system := system
  scheduler := Scheduler.depthFirst
  roots := BranchingTemporal.Starvation.roots

theorem run_eq (fuel : Nat) :
    run system Scheduler.depthFirst fuel
        (initial BranchingTemporal.Starvation.roots) =
      { events := List.replicate fuel ⟨.loop, 0⟩
        frontier := BranchingTemporal.Starvation.roots } := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      change
        tick system Scheduler.depthFirst
            (run system Scheduler.depthFirst fuel
              (initial BranchingTemporal.Starvation.roots)) =
          { events := List.replicate (fuel + 1) ⟨.loop, 0⟩
            frontier := BranchingTemporal.Starvation.roots }
      rw [inductionHypothesis]
      rw [List.replicate_succ']
      rfl

theorem stream_productive :
    StreamProductiveFor scenario EventObserver.value (fun _ => 0) := by
  intro demand
  refine ⟨demand, ?_⟩
  change
    (streamPrefix (fun _ => 0) demand).IsPrefix
      (EventObserver.value.observeList
        (run system Scheduler.depthFirst demand
          (initial BranchingTemporal.Starvation.roots)).events)
  rw [run_eq, streamPrefix_const, EventObserver.observeList_value]
  simp

theorem not_occurrence_fair : ¬ scenario.OccurrenceFair := by
  intro fair
  obtain ⟨fuel, selectedAnswer⟩ := fair .answer
    ⟨0, by simp [scenario, run, initial,
      BranchingTemporal.Starvation.roots]⟩
  change
    selected Scheduler.depthFirst
      (run system Scheduler.depthFirst fuel
        (initial BranchingTemporal.Starvation.roots)).frontier =
      some .answer at selectedAnswer
  rw [run_eq] at selectedAnswer
  simp [selected, Scheduler.depthFirst,
    BranchingTemporal.Starvation.roots] at selectedAnswer

end ProductiveStarvation

/-- A productive observed stream does not imply fairness for every live
occurrence. -/
theorem stream_productivity_does_not_imply_occurrence_fairness :
    StreamProductiveFor ProductiveStarvation.scenario EventObserver.value
        (fun _ => 0) ∧
      ¬ ProductiveStarvation.scenario.OccurrenceFair :=
  ⟨ProductiveStarvation.stream_productive,
    ProductiveStarvation.not_occurrence_fair⟩

/-! ### Recurrence and finite closure do not supply infinite productivity -/

theorem starvation_not_stream_productive :
    ¬ StreamProductiveFor starvationScenario EventObserver.value
      (fun _ => 42) := by
  intro productive
  obtain ⟨fuel, prefixEvidence⟩ := productive 1
  change
    (streamPrefix (fun _ => 42) 1).IsPrefix
      (EventObserver.value.observeList
        (run BranchingTemporal.Starvation.system Scheduler.depthFirst fuel
          (initial BranchingTemporal.Starvation.roots)).events) at prefixEvidence
  rw [BranchingTemporal.Starvation.depthFirst_run_fixed,
    EventObserver.observeList_value] at prefixEvidence
  simp [streamPrefix, initial] at prefixEvidence

/-- A recurring accepted loop can remain observationally silent forever. -/
theorem accepted_recurrence_does_not_imply_stream_productivity :
      starvationScenario.AcceptedSelectionRecurs
        (fun node => node = BranchingTemporal.Starvation.Node.loop) ∧
      ¬ StreamProductiveFor starvationScenario EventObserver.value
        (fun _ => 42) :=
  ⟨starvation_loop_selection_recurs, starvation_not_stream_productive⟩

theorem singleAnswer_events_length_le_one (fuel : Nat) :
    (singleAnswerScenario.snapshotAt fuel).events.length ≤ 1 := by
  cases fuel with
  | zero => simp [Scenario.snapshotAt, run, initial]
  | succ fuel =>
      change
        (run singleAnswerSystem Scheduler.breadthFirst (fuel + 1)
          (initial [()])).events.length ≤ 1
      rw [run_succ_from_tick]
      have closed :
          (tick singleAnswerSystem Scheduler.breadthFirst
            (initial [()])).frontier = [] := by
        rfl
      rw [run_eq_self_of_frontier_nil singleAnswerSystem
        Scheduler.breadthFirst _ closed fuel]
      decide

/-- Finite closure and exact finite-bag agreement do not promise an infinite
stream.  This scenario can supply one `42`, but never a demanded second one. -/
theorem finite_bag_completion_does_not_imply_stream_productivity :
    singleAnswerScenario.FinitelyCloses ∧
      singleAnswerScenario.ObservesBagAt 1 {42} ∧
      ¬ StreamProductiveFor singleAnswerScenario EventObserver.value
        (fun _ => 42) := by
  refine ⟨⟨1, singleAnswer_frontier_closed⟩,
    singleAnswer_observes_declared_bag, ?_⟩
  intro productive
  obtain ⟨fuel, prefixEvidence⟩ := productive 2
  have prefixLength := prefixEvidence.length_le
  rw [EventObserver.observeList_value] at prefixLength
  have observedBound := singleAnswer_events_length_le_one fuel
  simp [streamPrefix] at prefixLength
  omega

end Canaries

#print axioms Scenario.observed_prefix_after_resume
#print axioms Scenario.StreamProductiveFor.map
#print axioms Canaries.productive_fair_open_and_not_finite_bag
#print axioms Canaries.occurrence_fairness_does_not_imply_stream_productivity
#print axioms Canaries.stream_productivity_does_not_imply_occurrence_fairness
#print axioms Canaries.accepted_recurrence_does_not_imply_stream_productivity
#print axioms Canaries.finite_bag_completion_does_not_imply_stream_productivity

end Mettapedia.GSLT.Core.SearchStreamProductivity
