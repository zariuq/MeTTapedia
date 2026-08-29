import Mettapedia.GSLT.Core.AgeProtectedSchedule

/-!
# Age-priority schedules

An age-priority schedule is an occurrence-preserving portfolio with two
independently justified parts:

* an age lane supplies the fairness duty for unbounded search;
* a genuine priority lane deforms the selection order away from strict FIFO.

The priority lane is deliberately abstract.  Structural weight, KBO-flavoured
weight, valuation, compression gain, and learned complete permutations may all
inhabit it.  None gains authority to mint, duplicate, or discard occurrences.

The definition does not make this portfolio universally admissible.  Ordered
streams, bounded observations, effects, and physical capture remain separate
admission judgments.  Nor does it prescribe a physical frontier
representation.  It only records a useful age-plus-priority specialization of
the more generic `AgeProtectedSchedule`; it is neither GCL itself nor the
ambient evaluator default.
-/

namespace Mettapedia.GSLT.Core.AgePrioritySchedule

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.WeightedOccurrenceControl
open Mettapedia.GSLT.Core.AgeProtectedSchedule

universe uNode uAnswer

/-- A selection field whose queue discipline is observably not the FIFO age
discipline.  The witness is intentionally weaker than a score algebra: it
requires only one frontier on which the field changes transport order. -/
structure PriorityField (Node : Type uNode) where
  discipline : QueueDiscipline Node
  distinguishesAge :
    ∃ pending generated,
      discipline.integrate pending generated ≠
        QueueDiscipline.breadthFirst.integrate pending generated

namespace PriorityField

variable {Node : Type uNode}

/-- A genuine priority field cannot be strict breadth-first transport under a
different name. -/
theorem ne_breadthFirst (field : PriorityField Node) :
    field.discipline ≠ QueueDiscipline.breadthFirst := by
  intro equality
  obtain ⟨pending, generated, distinguishes⟩ := field.distinguishesAge
  apply distinguishes
  exact congrArg
    (fun discipline : QueueDiscipline Node =>
      discipline.integrate pending generated)
    equality

end PriorityField

/-- One occurrence-preserving portfolio, one FIFO age lane, and a distinct
priority lane.  Other lanes remain open. -/
structure Spec (Node : Type uNode) (count : Nat) [NeZero count] where
  schedule : AgeProtectedSchedule.Spec Node count
  priorityLane : Fin count
  priority : PriorityField Node
  priorityDiscipline :
    schedule.disciplines priorityLane = priority.discipline
  priority_ne_age : priorityLane ≠ schedule.ageLane

namespace Spec

variable {Node : Type uNode} {Answer : Type uAnswer} {count : Nat}
variable [NeZero count]

/-- The designated priority view is not its FIFO age view. -/
theorem priority_lane_not_breadthFirst (portfolio : Spec Node count) :
    portfolio.schedule.disciplines portfolio.priorityLane ≠
      QueueDiscipline.breadthFirst := by
  rw [portfolio.priorityDiscipline]
  exact portfolio.priority.ne_breadthFirst

/-- Start every prepared view from the same exact occurrence frontier. -/
def initial (portfolio : Spec Node count) (roots : List Node)
    (start : Fin count) : PortfolioSnapshot Node Answer count :=
  portfolio.schedule.initial roots start

/-- The age lane makes every live occurrence selectable after finite work,
independently of the priority field's bias. -/
theorem eventually_selects_live [DecidableEq Node]
    (portfolio : Spec Node count)
    (system : BranchingSystem Node Answer)
    (snapshot : PortfolioSnapshot Node Answer count)
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    ∃ fuel,
      target ∈
        (PortfolioSnapshot.run system portfolio.schedule.disciplines fuel
          snapshot).selections :=
  portfolio.schedule.eventually_selects_live system snapshot live

/-- In particular, every initially live occurrence is protected from
priority-field starvation. -/
theorem eventually_selects_root [DecidableEq Node]
    (portfolio : Spec Node count)
    (system : BranchingSystem Node Answer)
    (roots : List Node) (start : Fin count)
    {target : Node} (root : target ∈ roots) :
    ∃ fuel,
      target ∈
        (PortfolioSnapshot.run system portfolio.schedule.disciplines fuel
          (portfolio.initial (Answer := Answer) roots start)).selections := by
  apply portfolio.eventually_selects_live system _
  simpa [initial, AgeProtectedSchedule.Spec.initial,
    PortfolioSnapshot.initial, PortfolioFrontier.initial] using root

/-- Selection transports but does not alter the additive answer account. -/
theorem account_run [DecidableEq Node]
    (portfolio : Spec Node count)
    (system : BranchingSystem Node Answer)
    (denotation : AdditiveDenotation system)
    (fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count) :
    PortfolioSnapshot.account denotation
        (PortfolioSnapshot.run system portfolio.schedule.disciplines fuel
          snapshot) =
      PortfolioSnapshot.account denotation snapshot :=
  portfolio.schedule.account_run system denotation fuel snapshot

/-- A run which actually closes has the declared completed answer bag.
Fairness does not manufacture the closure premise. -/
theorem completed_denotation [DecidableEq Node]
    (portfolio : Spec Node count)
    (system : BranchingSystem Node Answer)
    (denotation : AdditiveDenotation system)
    (roots : List Node) (start : Fin count) (fuel : Nat)
    (complete :
      (PortfolioSnapshot.run system portfolio.schedule.disciplines fuel
        (portfolio.initial (Answer := Answer) roots start)).frontier.live = []) :
    eventBag
        (PortfolioSnapshot.run system portfolio.schedule.disciplines fuel
          (portfolio.initial (Answer := Answer) roots start)).events =
      foldValues denotation.value roots :=
  portfolio.schedule.completed_denotation system denotation roots start fuel
    complete

end Spec

/-! ## Minimal two-lane realization -/

/-- One priority lane and one FIFO age lane over the same occurrence store.
The pair is a semantic reference instance, not a claim about physical queue
layout or a fixed production ratio. -/
def paired (priority : PriorityField Node) : Spec Node 2 where
  schedule := {
    disciplines := fun lane =>
      if lane = (1 : Fin 2) then QueueDiscipline.breadthFirst
      else priority.discipline
    ageLane := 1
    ageDiscipline := by simp }
  priorityLane := 0
  priority := priority
  priorityDiscipline := by simp
  priority_ne_age := by
    change (0 : Fin 2) ≠ (1 : Fin 2)
    decide

/-! ## Positive and negative canaries -/

namespace Canaries

/-- Depth bias is a valid priority field when protected by a separate age
lane.  Its local ordering differs from FIFO, while the composite remains
fair. -/
def depthPriority : PriorityField Nat where
  discipline := QueueDiscipline.depthFirst
  distinguishesAge := ⟨[1], [2], by decide⟩

def depthAgePriority : Spec Nat 2 := paired depthPriority

/-- The first child creates fresh subwork while its sibling is still live.
Strict FIFO next selects the sibling; the depth-biased priority lane next
selects the fresh child. -/
def branchingSystem : BranchingSystem Nat Unit where
  emit _ := none
  successors
    | 0 => [1, 2]
    | 1 => [3]
    | _ => []

/-- The age-priority schedule is not strict level-order BFS: after the shared
first two steps, the priority turn selects fresh node `3`, while strict FIFO
selects pending node `2`. -/
theorem age_priority_differs_from_strict_breadth_first :
    (PortfolioSnapshot.run branchingSystem
        depthAgePriority.schedule.disciplines 3
        (depthAgePriority.initial (Answer := Unit) [0] 0)).selections = [0, 1, 3] ∧
      selected Scheduler.breadthFirst
          (run branchingSystem Scheduler.breadthFirst 2
            (Mettapedia.GSLT.Core.BranchingTemporal.initial [0])).frontier =
        some 2 := by
  decide

open Mettapedia.GSLT.Core.BranchingTemporal.Starvation

def starvationDepthPriority : PriorityField Node where
  discipline := QueueDiscipline.depthFirst
  distinguishesAge := ⟨[Node.answer], [Node.loop], by decide⟩

def starvationAgePriority : Spec Node 2 := paired starvationDepthPriority

/-- The age-protected priority schedule reaches the occurrence which bare
depth-first search starves forever. -/
theorem age_priority_reaches_dfs_starved_occurrence :
    ∃ fuel,
      Node.answer ∈
        (PortfolioSnapshot.run system
          starvationAgePriority.schedule.disciplines fuel
          (starvationAgePriority.initial (Answer := Nat) roots 0)).selections :=
  starvationAgePriority.eventually_selects_root system roots 0 (by simp [roots])

/-- Negative control: occurrence-preserving bare DFS remains lawful, but it
does not satisfy the age-protected schedule's liveness duty. -/
theorem bare_depth_first_still_not_fair :
    ¬ FairFrom system Scheduler.depthFirst roots :=
  depthFirst_not_fair

end Canaries

#print axioms PriorityField.ne_breadthFirst
#print axioms Spec.priority_lane_not_breadthFirst
#print axioms Spec.eventually_selects_live
#print axioms Spec.eventually_selects_root
#print axioms Spec.account_run
#print axioms Spec.completed_denotation
#print axioms Canaries.age_priority_differs_from_strict_breadth_first
#print axioms Canaries.age_priority_reaches_dfs_starved_occurrence
#print axioms Canaries.bare_depth_first_still_not_fair

end Mettapedia.GSLT.Core.AgePrioritySchedule
