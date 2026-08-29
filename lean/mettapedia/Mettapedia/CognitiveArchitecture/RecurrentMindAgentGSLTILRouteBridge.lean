import Mettapedia.CognitiveArchitecture.FairRecurrentMindAgentBackpressure
import Mettapedia.CognitiveArchitecture.FiniteRecurrentPremiseCost
import Mettapedia.GSLT.LanguageDef.GSLTILRecurrentRouteBridge

/-!
# Recurrent mind-agents in the GSLT-IL operational waist

The checked five-role cognitive portfolio already connects foreground
chaining, ECAN, incremental compression, PLN appraisal, and premise selection
through one recurrent controller.  This module shows that the same physical
occurrences also inhabit the common GSLT-IL operational waist.

The bridge is identity-sensitive.  The retained prefix erases exactly to the
existing finite route, and realizing that erased route gives exactly the
existing triggered-work batch used by parallel-wave admission.  A recurring
premise-selection receipt is located at its exact controller occurrence, so
its value, explicit choice, engine cost, and funding evidence are attached to
work on the retained route rather than to a parallel reconstruction.

Controller recurrence, occurrence-level scheduling fairness, parallel-wave
admission, and engine funding remain independent authorities.  Positive and
negative controls make those separations observable.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.RecurrentMindAgentGSLTILRouteBridge

open Mettapedia.CognitiveArchitecture.FairRecurrentMindAgentBackpressure
open Mettapedia.CognitiveArchitecture.FiniteRecurrentPremiseCost
open Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentBackpressure
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
open Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave.Canary
open Mettapedia.CognitiveArchitecture.RecurringValuedCostedPremiseService
open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.CognitiveArchitecture.TriggeredOccurrenceRouteRealization
open Mettapedia.CognitiveArchitecture.ValuedCostedPremiseService
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Core.WeightedOccurrenceControl
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
open Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteBridge

noncomputable section

/-! ## The checked recurrent portfolio as one retained route -/

/-- The accepted progress measure supplies both local edge authority and
Buechi recurrence for the canonical portfolio execution. -/
def auditedPortfolioRoute :
    AuditedRecurrentExecution portfolioStepAuthority foregroundAccepting
      portfolioClaim :=
  AuditedRecurrentExecution.ofAccepted portfolioStepAuthority
    foregroundAccepting portfolioClaim () portfolioMeasure
    portfolio_checker_accepts portfolioExecution

/-- The exact occurrence-retaining portfolio prefix at one demanded depth. -/
def retainedPortfolioPrefix (depth : Nat) :
    PathRetainingFiniteRoute
      (auditedRevisionTheory portfolioStepAuthority foregroundAccepting)
      (ControlledOccurrence portfolioTheory
        portfolioStepAuthority.Certificate)
      portfolioClaim.root :=
  AuditedRecurrentExecution.retainedPrefix portfolioStepAuthority
    foregroundAccepting portfolioClaim auditedPortfolioRoute depth

/-- The GSLT-IL route is a strict strengthening of the established portfolio
route, not a second implementation of it. -/
theorem retainedPortfolioPrefix_erases_to_checkedPrefix (depth : Nat) :
    (retainedPortfolioPrefix depth).erase = checkedPrefix depth :=
  retainedFinitePrefix_erases_to_finitePrefix portfolioStepAuthority
    foregroundAccepting portfolioClaim auditedPortfolioRoute.locallyValid
    portfolioExecution depth

/-- Triggered-space realization of the retained route is exactly the existing
generated mind-agent prefix. -/
theorem retainedPortfolioPrefix_realizes_generatedPrefix (depth : Nat) :
    portfolioCodec.realizeRoute foregroundAccepting
        (retainedPortfolioPrefix depth).erase =
      generatedPrefix depth := by
  rw [retainedPortfolioPrefix_erases_to_checkedPrefix]
  rfl

/-- Every requested portfolio prefix enters the path equipment and the
reachability institution at its exact depth and endpoint. -/
theorem retainedPortfolioPrefix_enters_operational_waist (depth : Nat) :
    ((retainedToExecutionPathSquare
      (auditedRevisionTheory portfolioStepAuthority foregroundAccepting)
      (ControlledOccurrence portfolioTheory
        portfolioStepAuthority.Certificate)).map
        (AuditedRecurrentExecution.prefixWitness portfolioStepAuthority
          foregroundAccepting portfolioClaim auditedPortfolioRoute
          depth)).length = depth /\
      portfolioClaim.root ∈ reachesTargetSentence
        (auditedRevisionTheory portfolioStepAuthority foregroundAccepting)
        (portfolioExecution.state depth) :=
  AuditedRecurrentExecution.prefix_enters_operational_waist
    portfolioStepAuthority foregroundAccepting portfolioClaim
    auditedPortfolioRoute depth

/-! ## The same first cycle earns operational and parallel interpretations -/

/-- The exact generated work used by the wave is the realization of the
retained five-edge execution path. -/
theorem retained_first_cycle_realizes_wave_batch :
    portfolioCodec.realizeRoute foregroundAccepting
        (retainedPortfolioPrefix 5).erase = cycleBatch := by
  rw [retainedPortfolioPrefix_realizes_generatedPrefix,
    cycleBatch_is_portfolio_prefix]

/-- One and the same checked first cycle has a five-edge operational path,
the exact typed generated batch, and complete-bag bulk admission. -/
theorem same_first_cycle_enters_path_and_parallel_wave :
    (retainedPortfolioPrefix 5).executionPath.length = 5 /\
      portfolioCodec.realizeRoute foregroundAccepting
          (retainedPortfolioPrefix 5).erase = cycleBatch /\
      (recurrentCycleWave.admission.certified.plan .general).activation =
        .bulk := by
  exact ⟨retainedFinitePrefix_executionPath_length portfolioStepAuthority
      foregroundAccepting portfolioClaim auditedPortfolioRoute.locallyValid
      portfolioExecution 5,
    retained_first_cycle_realizes_wave_batch,
    recurrentCycleWave.completeBag_dispatches_bulk rfl⟩

/-! ## Value, choice, cost, and funding attached to route occurrences -/

/-- The recurring premise-selection service is located at the exact retained
controller occurrence that generated it.  Its value-based choice and engine
cost are receipts on that work; an independently empty purse still refuses
the same invocation. -/
theorem premise_service_is_located_costed_and_not_self_funding (cycle : Nat) :
    sourceOccurrence cycle ∈
        (retainedPortfolioPrefix (schedulerEpoch cycle + 1)).occurrences /\
      (retainedPortfolioPrefix
        (schedulerEpoch cycle + 1)).executionPath.length =
          schedulerEpoch cycle + 1 /\
      selectedServicesAt cycle = {selectedOccurrenceAt cycle} /\
      costValuation.historyGrade (executionTraceAt cycle) = some exactSpent /\
      Nonempty
        (BatchSeparation EngineCost eventCost exactSpent
          (executionTraceAt cycle)) /\
      ¬ Nonempty
        (BatchSeparation EngineCost eventCost (0 : EngineCost)
          (executionTraceAt cycle)) := by
  refine ⟨?_, retainedFinitePrefix_executionPath_length
      portfolioStepAuthority foregroundAccepting portfolioClaim
      auditedPortfolioRoute.locallyValid portfolioExecution
      (schedulerEpoch cycle + 1), ?_, ?_, ?_, ?_⟩
  · change sourceOccurrence cycle ∈
      occurrencePrefix portfolioStepAuthority portfolioClaim
        portfolioExecution (schedulerEpoch cycle + 1)
    rw [occurrencePrefix]
    simp [sourceOccurrence]
  · exact (recurringPremiseReceipt cycle).exactChoice
  · exact (recurringPremiseReceipt cycle).exactCost
  · exact ⟨(recurringPremiseReceipt cycle).engineFunding⟩
  · exact zero_frame_refuses_next_trace cycle

/-! ## Recurrence and occurrence fairness are separate obligations -/

/-- The real portfolio supplies both controller recurrence and liveness of a
specific delayed foreground occurrence, but through independent witnesses. -/
theorem recurrent_route_and_occurrence_fairness_coexist :
    portfolioClaim.Meaning foregroundAccepting /\
      (forall depth,
        (retainedPortfolioPrefix depth).executionPath.length = depth) /\
      initialForeground ∈ ongoingAdmission.pending /\
      exists fuel,
        initialForeground ∈
          (PortfolioSnapshot.run continualSystem
            fairPortfolio.schedule.disciplines fuel
            (fairPortfolio.initial (Answer := Unit)
              (limitedCycle.pending ++ refreshedBackground) 0)).selections := by
  exact ⟨portfolio_checked_consequences.2,
    fun depth => retainedFinitePrefix_executionPath_length
      portfolioStepAuthority foregroundAccepting portfolioClaim
      auditedPortfolioRoute.locallyValid portfolioExecution depth,
    delayed_foreground_remains_live⟩

/-- A recurrent, generated route remains a countermodel to the claim that
recurrence itself schedules each occurrence: the hostile selector still
selects nothing. -/
theorem recurrence_does_not_mint_occurrence_selection :
    portfolioClaim.Meaning foregroundAccepting /\
      (let routeOccurrence := occurrenceAt portfolioStepAuthority
          portfolioClaim portfolioExecution 0
       let generated := portfolioCodec.realize routeOccurrence
       serviceSpace.Generated heartbeatTrace generated.generatedAt generated /\
         ¬ exists cycle, neverSelected cycle generated) :=
  ⟨portfolio_checked_consequences.2,
    RecurrentMindAgentPortfolio.generation_does_not_imply_selection⟩

#print axioms retainedPortfolioPrefix_erases_to_checkedPrefix
#print axioms retainedPortfolioPrefix_realizes_generatedPrefix
#print axioms retainedPortfolioPrefix_enters_operational_waist
#print axioms retained_first_cycle_realizes_wave_batch
#print axioms same_first_cycle_enters_path_and_parallel_wave
#print axioms premise_service_is_located_costed_and_not_self_funding
#print axioms recurrent_route_and_occurrence_fairness_coexist
#print axioms recurrence_does_not_mint_occurrence_selection

end

end Mettapedia.CognitiveArchitecture.RecurrentMindAgentGSLTILRouteBridge
