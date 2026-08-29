import Mettapedia.GSLT.Core.BranchingTemporal
import Mettapedia.GSLT.Core.TickAutomatonLaneRecurrence

/-!
# Semantic properties of search control

This module gives distinct names and proof types to four claims that a search
controller may satisfy:

* a lane schedule repeatedly pays its oldest lane;
* a branching run eventually selects every occurrence that becomes live;
* a finite run closes its frontier;
* a finite prefix observes a particular occurrence bag.

These claims are intentionally not fields of one monolithic `WellFormed`
predicate.  `CertifiedProperty` is a dependent property bag: its tag fixes the
exact proposition carried by its evidence.  In particular, a certificate for
one recurring accepted selection cannot be stored under the occurrence-
fairness tag, and a closure certificate cannot be stored as semantic agreement
without an independent `DeclaredBagMeaning`.

The canaries prove that the distinctions have content.  A depth-first run may
select one accepted loop forever while starving another live occurrence; a
fair breadth-first run may remain productively open forever; and a frontier may
close while disagreeing with an unrelated proposed answer bag.  The positive
bridge states the strongest general implication available here: closure plus
an additive denotation whose roots have the declared meaning yields exact bag
agreement.
-/

namespace Mettapedia.GSLT.Core.SearchControlProperties

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.TickAutomatonLaneRecurrence

universe uNode uAnswer

/-! ## Lane schedules -/

/-- The lane selected at each abstract controller tick.  This is policy data;
it does not by itself say how either lane acts on a live occurrence store. -/
structure LaneSchedule where
  laneAt : Nat → Lane

namespace LaneSchedule

/-- Every suffix contains an oldest-lane tick within the stated finite bound.
This is the exact arithmetic property certified for the ratio automaton. -/
def OldestRecursWithin (schedule : LaneSchedule) (bound : Nat) : Prop :=
  ∀ after, ∃ tick,
    after ≤ tick ∧ tick ≤ after + bound ∧ schedule.laneAt tick = .oldest

/-- The ratio tick automaton, exposed as a lane schedule. -/
def ratio (deep start : Nat) : LaneSchedule where
  laneAt tick := ratioLane deep (ratioTrajectory deep start tick)

/-- The ratio theorem supplies exactly a bounded lane-recurrence certificate;
no occurrence-store fairness is inferred here. -/
theorem ratio_oldest_recurs_within (deep start : Nat) :
    (ratio deep start).OldestRecursWithin deep := by
  intro after
  simpa [ratio, OldestRecursWithin] using
    ratio_oldest_lane_recurs_within deep start after

end LaneSchedule

/-! ## Branching-run scenarios and their independent properties -/

/-- The data required to state properties of one deterministic branching run. -/
structure Scenario (Node : Type uNode) (Answer : Type uAnswer) where
  system : BranchingSystem Node Answer
  scheduler : Scheduler Node
  roots : List Node

namespace Scenario

variable {Node : Type uNode} {Answer : Type uAnswer}

/-- Exact finite snapshot after `fuel` scheduler transitions. -/
def snapshotAt (scenario : Scenario Node Answer) (fuel : Nat) :
    Snapshot Node Answer :=
  run scenario.system scenario.scheduler fuel (initial scenario.roots)

/-- Occurrence selected next at one finite prefix. -/
def selectedAt (scenario : Scenario Node Answer) (fuel : Nat) : Option Node :=
  selected scenario.scheduler (scenario.snapshotAt fuel).frontier

/-- A Büchi-shaped property: every suffix contains a selected occurrence
accepted by `accepts`.  It says that some accepted selection recurs, not that
every live occurrence is eventually selected. -/
def AcceptedSelectionRecurs (scenario : Scenario Node Answer)
    (accepts : Node → Prop) : Prop :=
  ∀ after, ∃ tick, after ≤ tick ∧
    ∃ node, scenario.selectedAt tick = some node ∧ accepts node

/-- Per-occurrence fairness of the actual branching run. -/
def OccurrenceFair (scenario : Scenario Node Answer) : Prop :=
  FairFrom scenario.system scenario.scheduler scenario.roots

/-- The exact frontier is empty at this finite prefix. -/
def FrontierClosedAt (scenario : Scenario Node Answer) (fuel : Nat) : Prop :=
  (scenario.snapshotAt fuel).frontier = []

/-- Some finite prefix closes.  This is stronger than fairness and is false
for productive infinite computations. -/
def FinitelyCloses (scenario : Scenario Node Answer) : Prop :=
  ∃ fuel, scenario.FrontierClosedAt fuel

/-- The occurrence bag observed at one finite prefix equals `expected`.  This
does not claim that `expected` is the language's declared meaning. -/
def ObservesBagAt (scenario : Scenario Node Answer) (fuel : Nat)
    (expected : Multiset Answer) : Prop :=
  eventBag (scenario.snapshotAt fuel).events = expected

/-! ### A typed property bag -/

/-- Semantically distinct claims that may be certified about one scenario. -/
inductive Property (scenario : Scenario Node Answer) where
  | acceptedSelectionRecurs (accepts : Node → Prop)
  | occurrenceFair
  | frontierClosedAt (fuel : Nat)
  | observesBagAt (fuel : Nat) (expected : Multiset Answer)

/-- The proposition determined by a property tag. -/
def Property.Holds (scenario : Scenario Node Answer) :
    Property scenario → Prop
  | .acceptedSelectionRecurs accepts => scenario.AcceptedSelectionRecurs accepts
  | .occurrenceFair => scenario.OccurrenceFair
  | .frontierClosedAt fuel => scenario.FrontierClosedAt fuel
  | .observesBagAt fuel expected => scenario.ObservesBagAt fuel expected

/-- One property together with evidence of exactly the proposition named by
its tag. -/
structure CertifiedProperty (scenario : Scenario Node Answer) where
  property : Property scenario
  evidence : property.Holds scenario

/-- An extensible bag of independently certified control properties.  Missing
certificates remain unknown; absence from the bag is not negative evidence. -/
abbrev PropertyBag (scenario : Scenario Node Answer) :=
  List (CertifiedProperty scenario)

/-! ### Denotational authority is a separate bridge -/

/-- Independent declaration of the finite bag meaning of the scenario's
roots.  The additive denotation supplies the recursive semantic equations;
`rootsMeaning` identifies their value with the public declaration. -/
structure DeclaredBagMeaning (scenario : Scenario Node Answer) where
  denotation : AdditiveDenotation scenario.system
  expected : Multiset Answer
  rootsMeaning : foldValues denotation.value scenario.roots = expected

/-- Closure plus an independently supplied additive meaning yields exact bag
agreement.  Neither premise is reconstructed from the other. -/
theorem observesBagAt_of_frontierClosedAt
    (scenario : Scenario Node Answer)
    (meaning : DeclaredBagMeaning scenario) (fuel : Nat)
    (closed : scenario.FrontierClosedAt fuel) :
    scenario.ObservesBagAt fuel meaning.expected := by
  exact
    (completed_run_denotation scenario.system scenario.scheduler
      meaning.denotation scenario.roots fuel closed).trans meaning.rootsMeaning

end Scenario

/-! ## Positive and negative controls -/

namespace Canaries

open Scenario
open Mettapedia.GSLT.Core.BranchingTemporal.Starvation

/-- The starvation fixture as one semantically named scenario. -/
def starvationScenario : Scenario Node Nat where
  system := system
  scheduler := Scheduler.depthFirst
  roots := roots

/-- The loop occurrence is selected at every prefix, hence satisfies a
Büchi-shaped recurrence property. -/
theorem starvation_loop_selection_recurs :
    starvationScenario.AcceptedSelectionRecurs (· = Node.loop) := by
  intro after
  refine ⟨after, le_rfl, Node.loop, ?_, rfl⟩
  change selected Scheduler.depthFirst
    (run Starvation.system Scheduler.depthFirst after
      (initial Starvation.roots)).frontier = some Node.loop
  rw [depthFirst_run_fixed]
  rfl

/-- Recurrence of one accepted selection does not establish occurrence
fairness: the answer occurrence remains live and is never selected. -/
theorem accepted_selection_recurrence_does_not_imply_occurrence_fairness :
    starvationScenario.AcceptedSelectionRecurs (· = Node.loop) ∧
      ¬ starvationScenario.OccurrenceFair :=
  ⟨starvation_loop_selection_recurs, depthFirst_not_fair⟩

/-- Productive infinity under breadth-first scheduling. -/
def productiveScenario (answer : Answer) : Scenario Unit Answer where
  system := productiveLoopSystem answer
  scheduler := Scheduler.breadthFirst
  roots := [()]

/-- Productive infinity retains its unique live occurrence after every finite
prefix. -/
theorem productive_frontier_eq_singleton (answer : Answer) (fuel : Nat) :
    ((productiveScenario answer).snapshotAt fuel).frontier = [()] := by
  change
    (run (productiveLoopSystem answer) Scheduler.breadthFirst fuel
      (initial [()])).frontier = [()]
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      change
        (tick (productiveLoopSystem answer) Scheduler.breadthFirst
          (run (productiveLoopSystem answer) Scheduler.breadthFirst fuel
            (initial [()]))).frontier = [()]
      have reordered :
          Scheduler.breadthFirst.reorder
              (run (productiveLoopSystem answer) Scheduler.breadthFirst fuel
                (initial [()])).frontier = [()] := by
        simpa [Scheduler.breadthFirst] using inductionHypothesis
      unfold tick
      rw [reordered]
      rfl

/-- The productive loop is occurrence-fair: its only live occurrence is
eventually selected. -/
theorem productive_occurrence_fair (answer : Answer) :
    (productiveScenario answer).OccurrenceFair :=
  breadthFirst_fair (productiveLoopSystem answer) [()]

/-- The same fair run never has a finite closure certificate. -/
theorem productive_not_finitely_closes (answer : Answer) :
    ¬ (productiveScenario answer).FinitelyCloses := by
  rintro ⟨fuel, closed⟩
  rw [FrontierClosedAt, productive_frontier_eq_singleton] at closed
  simp at closed

/-- Per-occurrence fairness therefore does not imply finite completion. -/
theorem occurrence_fairness_does_not_imply_finite_closure (answer : Answer) :
    (productiveScenario answer).OccurrenceFair ∧
      ¬ (productiveScenario answer).FinitelyCloses :=
  ⟨productive_occurrence_fair answer, productive_not_finitely_closes answer⟩

/-- Productive infinity also has no finite additive bag meaning.  Its lawful
observations are prefixes or coinductive streams, not a fabricated completed
bag. -/
theorem productive_has_no_declared_finite_bag_meaning (answer : Answer) :
    ¬ Nonempty (DeclaredBagMeaning (productiveScenario answer)) := by
  rintro ⟨meaning⟩
  exact no_finite_denotation_productiveLoop answer ⟨meaning.denotation⟩

/-- A one-step computation with one answer. -/
def singleAnswerSystem : BranchingSystem Unit Nat where
  emit _ := some 42
  successors _ := []

def singleAnswerScenario : Scenario Unit Nat where
  system := singleAnswerSystem
  scheduler := Scheduler.breadthFirst
  roots := [()]

/-- Independent additive semantics for the single-answer system. -/
def singleAnswerDenotation : AdditiveDenotation singleAnswerSystem where
  value _ := {42}
  unfold _ := by
    simp [singleAnswerSystem, optionBag, foldValues]

def singleAnswerMeaning : DeclaredBagMeaning singleAnswerScenario where
  denotation := singleAnswerDenotation
  expected := {42}
  rootsMeaning := by
    simp [singleAnswerScenario, singleAnswerDenotation, foldValues]

theorem singleAnswer_frontier_closed :
    singleAnswerScenario.FrontierClosedAt 1 := by
  rfl

theorem singleAnswer_observes_declared_bag :
    singleAnswerScenario.ObservesBagAt 1 {42} := by
  exact observesBagAt_of_frontierClosedAt singleAnswerScenario
    singleAnswerMeaning 1 singleAnswer_frontier_closed

/-- Closure alone does not license an arbitrary proposed meaning. -/
theorem singleAnswer_not_observes_wrong_bag :
    ¬ singleAnswerScenario.ObservesBagAt 1 {7} := by
  intro wrong
  have bagEquality : ({42} : Multiset Nat) = {7} :=
    singleAnswer_observes_declared_bag.symm.trans wrong
  exact absurd (Multiset.singleton_inj.mp bagEquality) (by decide)

/-- A small dependent property bag whose entries cannot be confused by name:
the same scenario has a closure certificate and the matching observation
certificate, while the preceding theorem excludes the wrong observation. -/
def singleAnswerPropertyBag : PropertyBag singleAnswerScenario :=
  [⟨.frontierClosedAt 1, singleAnswer_frontier_closed⟩,
   ⟨.observesBagAt 1 {42}, singleAnswer_observes_declared_bag⟩]

end Canaries

#print axioms LaneSchedule.ratio_oldest_recurs_within
#print axioms Scenario.observesBagAt_of_frontierClosedAt
#print axioms Canaries.starvation_loop_selection_recurs
#print axioms
  Canaries.accepted_selection_recurrence_does_not_imply_occurrence_fairness
#print axioms Canaries.productive_frontier_eq_singleton
#print axioms Canaries.occurrence_fairness_does_not_imply_finite_closure
#print axioms Canaries.productive_has_no_declared_finite_bag_meaning
#print axioms Canaries.singleAnswer_not_observes_wrong_bag

end Mettapedia.GSLT.Core.SearchControlProperties
