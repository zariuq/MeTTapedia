import Mettapedia.CognitiveArchitecture.ForegroundChainingClosureBoundary
import Mettapedia.CognitiveArchitecture.RecurrentMindAgentStreamProductivity

/-!
# Finite foreground closure inside an open mind-agent ecology

A foreground cognitive task and its ambient organizational ecology have
different completion disciplines.  The worked premise-service task reaches a
quiescent solved store after two selected activations.  The recurrent
foreground/background portfolio, by contrast, deliberately keeps a live next
epoch while every resident role remains observable on demand.

This file connects those two existing results without identifying their
clocks or stores.  Local task completion therefore neither shuts down the
ambient ecology nor grants it semantic authority over the completed result.
Conversely, asking for a complete bag from an intentionally recurrent ecology
does not manufacture finite closure.

The result is an execution-topology boundary.  It does not claim that the
current native runtime has already mapped these certified activations onto OS
threads, nor that the recurrent role occurrences themselves fulfill the
domain services they name.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.NestedMindAgentExecutionBoundary

open Mettapedia.CognitiveArchitecture.ForegroundChainingClosureBoundary
open Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentStreamProductivity
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.SearchControlProperties
open Mettapedia.GSLT.Core.SearchStreamProductivity
open Mettapedia.GSLT.Core.SearchStreamProductivity.Scenario
open Mettapedia.GSLT.Dynamics.SpaceExecutionClosureBoundary

noncomputable section

/-! ## Ambient recurrence beyond every local boundary -/

/-- Every foreground or background role appears again after any nominated
epoch.  The witness is derived from the checked five-role cycle rather than
from an independent fairness assumption. -/
theorem every_role_recurs_after
    (role : Role) (start : Nat) :
    ∃ epoch, start ≤ epoch ∧
      (generatedOccurrenceAt epoch).resident = role := by
  refine ⟨5 * start + roleOffset role, ?_, ?_⟩
  · omega
  · exact generatedOccurrenceAt_role_slot role start

/-- In particular, completing a scoped foreground task cannot cancel future
ECAN, compression, PLN, or premise-selection activations in the independent
ambient route. -/
theorem all_background_roles_recur_after (start : Nat) :
    (∃ epoch, start ≤ epoch ∧
      (generatedOccurrenceAt epoch).resident = .ecan) ∧
    (∃ epoch, start ≤ epoch ∧
      (generatedOccurrenceAt epoch).resident = .incrementalCompression) ∧
    (∃ epoch, start ≤ epoch ∧
      (generatedOccurrenceAt epoch).resident = .pln) ∧
    (∃ epoch, start ≤ epoch ∧
      (generatedOccurrenceAt epoch).resident = .premiseSelection) := by
  exact ⟨every_role_recurs_after .ecan start,
    every_role_recurs_after .incrementalCompression start,
    every_role_recurs_after .pln start,
    every_role_recurs_after .premiseSelection start⟩

/-! ## The nested closure/productivity crown -/

/-- The real foreground chaining task closes after the background premise
service has enabled it, while the ambient mixed-role ecology remains open and
each role remains independently stream-productive.  These are compatible
facts because they quantify over two explicitly scoped executions. -/
theorem finite_foreground_closure_coexists_with_open_productive_ecology :
    Nonempty
        (ActivationDriver.FiniteClosure foregroundDriver admittedSnapshot ()) ∧
      foregroundDriver.toHostedDriver.runReport admittedSnapshot () 2 =
        .completed solvedSnapshot () ∧
      solvedSnapshot.events =
        [⟨goalFrom (selectedOccurrenceAt 0), ProofResult.proved⟩] ∧
      ¬ generationScenario.FinitelyCloses ∧
      (∀ role : Role,
        StreamProductiveFor generationScenario (roleSignalObserver role)
          (fun _ => role)) ∧
      ∀ role start, ∃ epoch, start ≤ epoch ∧
        (generatedOccurrenceAt epoch).resident = role := by
  exact ⟨⟨solvedClosure⟩, two_activations_complete,
    background_premise_service_unblocks_foreground.2.2.2.1,
    generation_not_finitely_closes, all_five_roles_stream_productive,
    every_role_recurs_after⟩

/-- Ordered finite pulls are the honest observation mode for the open
ecology: every requested finite prefix arrives, but a next epoch remains
live. -/
theorem ambient_ordered_pull_is_productive_and_open :
    dispatch
        ({ completion := .orderedStream, guard := none } :
          ObservationDemand Unit)
        .general .singletonOnly =
          { readout := .orderedStream, activation := .controlled } ∧
      StreamProductiveFor generationScenario
        EventObserver.value generatedOccurrenceAt ∧
      ¬ generationScenario.FinitelyCloses := by
  exact ⟨ordered_stream_demand_is_controlled_and_productive.1,
    ordered_stream_demand_is_controlled_and_productive.2,
    generation_not_finitely_closes⟩

/-! ## Negative controls -/

/-- A complete-bag observer and a single-path activation license still do not
turn an intentionally recurrent ecology into a finite computation.  Demand
cannot rewrite the temporal contract. -/
theorem ambient_complete_bag_demand_does_not_force_shutdown :
    dispatch
        ({ completion := .completeBag, guard := none } :
          ObservationDemand Unit)
        .singlePath .serializable =
          { readout := .completeBag, activation := .singlePath } ∧
      ¬ generationScenario.FinitelyCloses :=
  complete_bag_single_path_still_does_not_close

/-- More foreground fuel cannot replace the missing background premise
service.  Ambient assistance is productive work, not an assumption that the
foreground scheduler may mint locally. -/
theorem local_fuel_does_not_mint_background_assistance :
    Mettapedia.GSLT.Core.GivenClauseLoop.Snapshot.run
        Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService.chainingSystem
        Mettapedia.GSLT.Core.GivenClauseLoop.Snapshot.breadthOnly 2
        stalledSnapshot = stalledSnapshot ∧
      (Mettapedia.GSLT.Core.GivenClauseLoop.Snapshot.run
        Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService.chainingSystem
        Mettapedia.GSLT.Core.GivenClauseLoop.Snapshot.breadthOnly 2
        stalledSnapshot).events = [] :=
  closure_demand_cannot_replace_background_service

#print axioms every_role_recurs_after
#print axioms all_background_roles_recur_after
#print axioms finite_foreground_closure_coexists_with_open_productive_ecology
#print axioms ambient_ordered_pull_is_productive_and_open
#print axioms ambient_complete_bag_demand_does_not_force_shutdown
#print axioms local_fuel_does_not_mint_background_assistance

end

end Mettapedia.CognitiveArchitecture.NestedMindAgentExecutionBoundary
