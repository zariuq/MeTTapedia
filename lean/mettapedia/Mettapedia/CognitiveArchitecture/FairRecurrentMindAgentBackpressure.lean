import Mettapedia.CognitiveArchitecture.RecurrentMindAgentBackpressure
import Mettapedia.CognitiveArchitecture.RecurringValuedCostedPremiseService
import Mettapedia.GSLT.Core.AgePrioritySchedule
import Mettapedia.GSLT.Core.ResourceBackpressureScheduling

/-!
# Fair backpressure for a continually regenerating mind-agent portfolio

This discriminator connects three independently justified layers:

* checked five-periodic controller occurrences generate the next exact
  occurrence of each cognitive role;
* finite resource admission retains an exact foreground residual while fresh
  background work arrives behind it in the FIFO age view; and
* an age-plus-priority portfolio eventually selects that foreground
  occurrence even though every selected service generates another occurrence.

The priority lane deliberately uses newest-first transport, which increases
the foreground occurrence's debt when fresh background work arrives.  It is
lawful as a complete occurrence permutation but is not the fairness witness.
The separate FIFO age lane supplies that duty.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.FairRecurrentMindAgentBackpressure

noncomputable section

open Mettapedia.CognitiveArchitecture.RecurrentMindAgentBackpressure
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
open Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave.Canary
open Mettapedia.CognitiveArchitecture.RecurringValuedCostedPremiseService
open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.CognitiveArchitecture.TriggeredOccurrenceRouteRealization
open Mettapedia.GSLT.Core.AgePrioritySchedule
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.ResourceBackpressureScheduling
open Mettapedia.GSLT.Core.WeightedOccurrenceControl
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute

/-! ## Every regenerated role remains a checked controller occurrence -/

/-- One later cycle of the same exact resident occurrence. -/
def nextGeneration (item : Item) : Item :=
  { generatedAt := item.generatedAt + 5
    trigger := item.trigger
    resident := item.resident }

theorem portfolioExecution_state_add_five (epoch : Nat) :
    portfolioExecution.state (epoch + 5) = portfolioExecution.state epoch := by
  change (nextRole^[epoch + 5]) .foregroundChaining =
    (nextRole^[epoch]) .foregroundChaining
  rw [Function.iterate_add_apply, nextRole_five]
  rfl

/-- Advancing a realized occurrence by one controller cycle is exactly the
realization of the checked source occurrence five epochs later. -/
theorem nextGeneration_checked_source (epoch : Nat) :
    nextGeneration
        (portfolioCodec.realize
          (occurrenceAt portfolioStepAuthority portfolioClaim
            portfolioExecution epoch)) =
      portfolioCodec.realize
        (occurrenceAt portfolioStepAuthority portfolioClaim
          portfolioExecution (epoch + 5)) := by
  change
    TriggeredOccurrence.mk (epoch + 5) ()
        (nextRole (portfolioExecution.state epoch)) =
      TriggeredOccurrence.mk (epoch + 5) ()
        (nextRole (portfolioExecution.state (epoch + 5)))
  rw [portfolioExecution_state_add_five]

/-- Arbitrarily many regenerated descendants remain exact checked controller
occurrences, not scheduler-minted role labels. -/
theorem iterate_nextGeneration_checked_source (round epoch : Nat) :
    (nextGeneration^[round])
        (portfolioCodec.realize
          (occurrenceAt portfolioStepAuthority portfolioClaim
            portfolioExecution epoch)) =
      portfolioCodec.realize
        (occurrenceAt portfolioStepAuthority portfolioClaim
          portfolioExecution (epoch + 5 * round)) := by
  induction round with
  | zero => simp
  | succ round inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis,
        nextGeneration_checked_source]
      congr 2

theorem nextGeneration_is_authored_space_generation (item : Item) :
    serviceSpace.Generated heartbeatTrace (item.generatedAt + 5)
      (nextGeneration item) := by
  simp [Space.Generated, nextGeneration, heartbeatTrace, serviceSpace]

/-! ## One overloaded round with continuing arrivals -/

/-- The two serviced background roles recur as fresh work behind the old
residual. -/
def refreshedBackground : List Item :=
  limitedCycle.admitted.map nextGeneration

theorem refreshedBackground_is_next_checked_prefix :
    refreshedBackground = ((generatedPrefix 10).drop 5).take 2 := by
  decide

def initialForeground : Item :=
  ⟨4, (), .foregroundChaining⟩

theorem initialForeground_is_old_residual :
    initialForeground ∈ limitedCycle.pending := by
  decide

/-- A second two-slot round services PLN and premise selection, retains the
old foreground occurrence, and queues the fresh ECAN/compression occurrences
behind it. -/
def ongoingAdmission :=
  fifoAdmission 2 limitedCycle.pending refreshedBackground

theorem ongoingAdmission_exact_role_partition :
    ongoingAdmission.admitted.map (fun item => item.resident) =
        [.pln, .premiseSelection] /\
      ongoingAdmission.pending.map (fun item => item.resident) =
        [.foregroundChaining, .ecan, .incrementalCompression] := by
  decide

theorem foreground_arrival_ageDebt_is_unchanged :
    QueueDiscipline.ageDebt
        (QueueDiscipline.breadthFirst.integrate limitedCycle.pending
          refreshedBackground) initialForeground =
      QueueDiscipline.ageDebt limitedCycle.pending initialForeground :=
  generated_work_does_not_increase_existing_ageDebt _ _
    initialForeground_is_old_residual

/-- Newest-first transport is occurrence-preserving but puts both fresh
background occurrences ahead of the old foreground occurrence. -/
theorem newest_first_arrivals_increase_foreground_debt :
    QueueDiscipline.ageDebt
        (QueueDiscipline.depthFirst.integrate limitedCycle.pending
          refreshedBackground) initialForeground >
      QueueDiscipline.ageDebt limitedCycle.pending initialForeground := by
  decide

/-! ## Priority plus an independent age lane -/

def freshnessPriority : PriorityField Item where
  discipline := QueueDiscipline.depthFirst
  distinguishesAge :=
    ⟨limitedCycle.pending, refreshedBackground, by decide⟩

def fairPortfolio :
    Mettapedia.GSLT.Core.AgePrioritySchedule.Spec Item 2 :=
  paired freshnessPriority

/-- Every selected cognitive occurrence produces its exact same-role
occurrence in the next checked controller cycle.  The system therefore never
runs out of background organizational work merely because one item ran. -/
def continualSystem : BranchingSystem Item Unit where
  successors item := [nextGeneration item]
  emit _ := none

/-- The old foreground occurrence is eventually selected even while every
service selection produces fresh work and the priority lane prefers fresh
work. -/
theorem fair_age_lane_eventually_selects_foreground :
    ∃ fuel,
      initialForeground ∈
        (PortfolioSnapshot.run continualSystem
          fairPortfolio.schedule.disciplines fuel
          (fairPortfolio.initial (Answer := Unit)
            (limitedCycle.pending ++ refreshedBackground) 0)).selections := by
  exact existing_eventually_selected fairPortfolio.schedule continualSystem
    limitedCycle.pending refreshedBackground 0
    initialForeground_is_old_residual

/-- Finite admission and unbounded liveness remain distinct facts: the
foreground occurrence is delayed by the current two-slot decision but
protected by the composite schedule. -/
theorem delayed_foreground_remains_live :
    initialForeground ∈ ongoingAdmission.pending /\
      ∃ fuel,
        initialForeground ∈
          (PortfolioSnapshot.run continualSystem
            fairPortfolio.schedule.disciplines fuel
            (fairPortfolio.initial (Answer := Unit)
              (limitedCycle.pending ++ refreshedBackground) 0)).selections := by
  exact ⟨by decide, fair_age_lane_eventually_selects_foreground⟩

/-- The priority lane is genuinely distinct from FIFO; it cannot be mistaken
for the fairness lane under another name. -/
theorem priority_lane_is_not_age_lane :
    fairPortfolio.schedule.disciplines fairPortfolio.priorityLane ≠
      (QueueDiscipline.breadthFirst : QueueDiscipline Item) :=
  fairPortfolio.priority_lane_not_breadthFirst

#print axioms portfolioExecution_state_add_five
#print axioms nextGeneration_checked_source
#print axioms iterate_nextGeneration_checked_source
#print axioms nextGeneration_is_authored_space_generation
#print axioms refreshedBackground_is_next_checked_prefix
#print axioms ongoingAdmission_exact_role_partition
#print axioms foreground_arrival_ageDebt_is_unchanged
#print axioms newest_first_arrivals_increase_foreground_debt
#print axioms fair_age_lane_eventually_selects_foreground
#print axioms delayed_foreground_remains_live
#print axioms priority_lane_is_not_age_lane

end
end Mettapedia.CognitiveArchitecture.FairRecurrentMindAgentBackpressure
