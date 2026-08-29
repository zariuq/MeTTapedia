import Mettapedia.GSLT.Core.WeightedOccurrenceControl

/-!
# Age-protected priority schedules

A priority discipline need not be fair in isolation.  Depth bias, KBO,
valuation, compression guidance, and learned complete permutations are all
lawful occurrence-preserving disciplines even when one of them can starve a
live occurrence.

Fairness may instead be established by the schedule which uses those
disciplines.  An `AgeProtectedSchedule` identifies one FIFO age lane in an
otherwise arbitrary finite portfolio.  The existing finite-debt theorem then
proves that every live occurrence is eventually selected.  No proof obligation
is imposed on the other lanes.

The theorem is unbounded: a finite resource cutoff still yields an incomplete
observation unless the frontier actually closes.  Thus an age turn every ten
thousand priority turns is fair as a mathematical schedule, while a run stopped
before that turn remains exhausted rather than complete.
-/

namespace Mettapedia.GSLT.Core.AgeProtectedSchedule

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.WeightedOccurrenceControl

universe uNode uAnswer

/-- A finite occurrence-preserving portfolio with one identified FIFO age
lane.  Other lanes are deliberately unconstrained beyond preservation. -/
structure Spec (Node : Type uNode) (count : Nat) [NeZero count] where
  disciplines : Fin count -> QueueDiscipline Node
  ageLane : Fin count
  ageDiscipline : disciplines ageLane = QueueDiscipline.breadthFirst

namespace Spec

variable {Node : Type uNode} {Answer : Type uAnswer} {count : Nat}
variable [NeZero count]

/-- Start all views from one exact occurrence frontier. -/
def initial (schedule : Spec Node count) (roots : List Node)
    (start : Fin count) : PortfolioSnapshot Node Answer count :=
  PortfolioSnapshot.initial schedule.disciplines roots start

/-- Every occurrence live in an arbitrary resumable snapshot is selected
after finitely many steps.  This liveness proof belongs to the composite
schedule; no priority lane is assumed fair. -/
theorem eventually_selects_live [DecidableEq Node]
    (schedule : Spec Node count)
    (system : BranchingSystem Node Answer)
    (snapshot : PortfolioSnapshot Node Answer count)
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    ∃ fuel,
      target ∈
        (PortfolioSnapshot.run system schedule.disciplines fuel snapshot).selections :=
  PortfolioSnapshot.roundRobin_with_breadthFirst_fair_from_snapshot
    system schedule.disciplines schedule.ageLane schedule.ageDiscipline
      snapshot live

/-- In particular, every root occurrence is selected under the age-protected
schedule. -/
theorem eventually_selects_root [DecidableEq Node]
    (schedule : Spec Node count)
    (system : BranchingSystem Node Answer)
    (roots : List Node) (start : Fin count)
    {target : Node} (root : target ∈ roots) :
    ∃ fuel,
      target ∈
        (PortfolioSnapshot.run system schedule.disciplines fuel
          (schedule.initial (Answer := Answer) roots start)).selections := by
  apply schedule.eventually_selects_live system _
  simpa [initial, PortfolioSnapshot.initial, PortfolioFrontier.initial]
    using root

/-- Selection policy changes transport the latent answer account without
changing it.  This is the conserved quantity of the portfolio. -/
theorem account_tick [DecidableEq Node]
    (schedule : Spec Node count)
    (system : BranchingSystem Node Answer)
    (denotation : AdditiveDenotation system)
    (snapshot : PortfolioSnapshot Node Answer count) :
    PortfolioSnapshot.account denotation
        (PortfolioSnapshot.tick system schedule.disciplines snapshot) =
      PortfolioSnapshot.account denotation snapshot :=
  PortfolioSnapshot.account_tick system schedule.disciplines denotation snapshot

/-- The same answer account is conserved across every finite scheduled
prefix, independently of which priority disciplines occupy the non-age
lanes. -/
theorem account_run [DecidableEq Node]
    (schedule : Spec Node count)
    (system : BranchingSystem Node Answer)
    (denotation : AdditiveDenotation system)
    (fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count) :
    PortfolioSnapshot.account denotation
        (PortfolioSnapshot.run system schedule.disciplines fuel snapshot) =
      PortfolioSnapshot.account denotation snapshot :=
  PortfolioSnapshot.account_run system schedule.disciplines denotation
    fuel snapshot

/-- A finite scheduled prefix cannot silently discard a live occurrence: the
occurrence either remains in the shared live store or appears in the exact
selection receipts. -/
theorem live_or_selected_after_run [DecidableEq Node]
    (schedule : Spec Node count)
    (system : BranchingSystem Node Answer)
    (fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count)
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    target ∈
        (PortfolioSnapshot.run system schedule.disciplines fuel snapshot).frontier.live ∨
      target ∈
        (PortfolioSnapshot.run system schedule.disciplines fuel snapshot).selections :=
  PortfolioSnapshot.live_or_selected_after_run system schedule.disciplines
    fuel snapshot live

/-- If an age-protected run actually closes, its emitted occurrence bag is the
declared denotation.  Fairness does not manufacture the closure premise. -/
theorem completed_denotation [DecidableEq Node]
    (schedule : Spec Node count)
    (system : BranchingSystem Node Answer)
    (denotation : AdditiveDenotation system)
    (roots : List Node) (start : Fin count) (fuel : Nat)
    (complete :
      (PortfolioSnapshot.run system schedule.disciplines fuel
        (schedule.initial (Answer := Answer) roots start)).frontier.live = []) :
    eventBag
        (PortfolioSnapshot.run system schedule.disciplines fuel
          (schedule.initial (Answer := Answer) roots start)).events =
      foldValues denotation.value roots :=
  PortfolioSnapshot.completed_run_denotation system schedule.disciplines
    denotation roots start fuel complete

end Spec

/-! ## A finite priority-to-age ratio -/

/-- Use `priorityTurns` arbitrary-priority lanes followed by one FIFO age
lane.  Repeated lanes specify a schedule ratio, not distinct semantic
authorities. -/
def priorityAgeDisciplines (priorityTurns : Nat)
    (priority : QueueDiscipline Node) :
    Fin (priorityTurns + 1) -> QueueDiscipline Node :=
  fun lane =>
    if lane = Fin.last priorityTurns then QueueDiscipline.breadthFirst
    else priority

@[simp] theorem priorityAgeDisciplines_ageLane
    (priorityTurns : Nat) (priority : QueueDiscipline Node) :
    priorityAgeDisciplines priorityTurns priority (Fin.last priorityTurns) =
      QueueDiscipline.breadthFirst := by
  simp [priorityAgeDisciplines]

/-- Build an age-protected schedule around any occurrence-preserving priority
discipline.  The priority discipline supplies no fairness proof. -/
def withPriorityShare (priorityTurns : Nat)
    (priority : QueueDiscipline Node) : Spec Node (priorityTurns + 1) where
  disciplines := priorityAgeDisciplines priorityTurns priority
  ageLane := Fin.last priorityTurns
  ageDiscipline := priorityAgeDisciplines_ageLane priorityTurns priority

/-- Depth-biased traversal is one specialization of the generic schedule,
not the ambient meaning of search. -/
def depthBiased (depthTurns : Nat) : Spec Node (depthTurns + 1) :=
  withPriorityShare depthTurns QueueDiscipline.depthFirst

namespace Canaries

open Mettapedia.GSLT.Core.BranchingTemporal.Starvation

/-- One depth-biased turn followed by one age turn reaches the occurrence
which pure DFS starves. -/
theorem depthBiased_reaches_starved_answer :
    ∃ fuel,
      Node.answer ∈
        (PortfolioSnapshot.run system
          (depthBiased (Node := Node) 1).disciplines fuel
          ((depthBiased (Node := Node) 1).initial
            (Answer := Nat) roots 0)).selections := by
  exact (depthBiased (Node := Node) 1).eventually_selects_root
    system roots 0 (by simp [roots])

/-- The corresponding pure depth discipline remains lawful but lacks the
same liveness property on this witness. -/
theorem pureDepth_still_not_fair :
    ¬ Mettapedia.GSLT.Core.BranchingTemporal.FairFrom
      system Scheduler.depthFirst roots :=
  depthFirst_not_fair

end Canaries

#print axioms Spec.eventually_selects_live
#print axioms Spec.eventually_selects_root
#print axioms Spec.account_tick
#print axioms Spec.account_run
#print axioms Spec.live_or_selected_after_run
#print axioms Spec.completed_denotation
#print axioms Canaries.depthBiased_reaches_starved_answer
#print axioms Canaries.pureDepth_still_not_fair

end Mettapedia.GSLT.Core.AgeProtectedSchedule
