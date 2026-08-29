import Mettapedia.CognitiveArchitecture.RecurrentMindAgentGSLTILRouteBridge
import Mettapedia.GSLT.Core.ObservationDemandControl
import Mettapedia.GSLT.LanguageDef.GSLTILRecurrentRouteStreamPresentation

/-!
# Stream productivity of the recurrent mind-agent route

The checked foreground/background portfolio already provides a coherent cone
of retained GSLT-IL routes.  This module presents that same cone as a
chronological branching scenario and proves observer-indexed productivity of
the generated-work stream.

No second cognitive execution is introduced.  Event `index` is exactly the
triggered-space realization of the retained controlled occurrence at that
index.  Consequently, observing `depth` events gives exactly the established
`generatedPrefix depth`, which in turn is exactly the realization of the
retained GSLT-IL route.

The result is intentionally scoped to generated and selected work
occurrences.  It does not promote route generation to proof-relevant service
fulfillment, payment, semantic truth, or ambient-state mutation.  Those
remain separately certified effects of the corresponding mind-agent.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.RecurrentMindAgentStreamProductivity

open Mettapedia.CognitiveArchitecture.RecurrentMindAgentGSLTILRouteBridge
open Mettapedia.CognitiveArchitecture.FairRecurrentMindAgentBackpressure
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
open Mettapedia.CognitiveArchitecture.RecurringValuedCostedPremiseService
open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.CognitiveArchitecture.TriggeredOccurrenceRouteRealization
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.SearchControlProperties
open Mettapedia.GSLT.Core.SearchStreamProductivity
open Mettapedia.GSLT.Core.SearchStreamProductivity.Scenario
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
open Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteStreamPresentation

noncomputable section

/-! ## The retained occurrence cone as a chronological scenario -/

/-- The exact generated mind-agent occurrence attached to controller epoch
`index`. -/
def generatedOccurrenceAt (index : Nat) : Occurrence :=
  realizedAt portfolioStepAuthority portfolioClaim portfolioExecution
    portfolioCodec.realize index

/-- The controlled-occurrence prefix itself is the chronological enumeration
of the exact indexed controller actions. -/
theorem occurrencePrefix_eq_range_map (depth : Nat) :
    occurrencePrefix portfolioStepAuthority portfolioClaim portfolioExecution
        depth =
      (List.range depth).map
        (occurrenceAt portfolioStepAuthority portfolioClaim portfolioExecution) := by
  exact
    Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteStreamPresentation.occurrencePrefix_eq_range_map
      portfolioStepAuthority portfolioClaim portfolioExecution depth

/-- The established generated prefix is the natural-index enumeration of the
same exact realized controlled occurrences. -/
theorem generatedPrefix_eq_range_map (depth : Nat) :
    generatedPrefix depth =
      (List.range depth).map generatedOccurrenceAt := by
  simp [generatedPrefix, Codec.realizeRoute, checkedPrefix, finitePrefix,
    occurrencePrefix_eq_range_map, generatedOccurrenceAt, realizedAt, List.map_map,
    Function.comp_def]

/-- A deterministic coalgebraic view of the retained route cone.  The only
live node is the next controller epoch. -/
def generationSystem : BranchingSystem Nat Occurrence :=
  streamSystem portfolioStepAuthority portfolioClaim portfolioExecution
    portfolioCodec.realize

def generationScenario : Scenario Nat Occurrence :=
  streamScenario portfolioStepAuthority portfolioClaim portfolioExecution
    portfolioCodec.realize

/-- Exact finite snapshots retain chronological origin indices as well as
generated occurrence identities. -/
theorem generation_run_eq (fuel : Nat) :
    run generationSystem Scheduler.breadthFirst fuel (initial [0]) =
      { events := (List.range fuel).map
          (fun index => ⟨index, generatedOccurrenceAt index⟩)
        frontier := [fuel] } := by
  exact stream_run_eq portfolioStepAuthority portfolioClaim portfolioExecution
    portfolioCodec.realize fuel

theorem generation_frontier_eq_singleton (fuel : Nat) :
    (generationScenario.snapshotAt fuel).frontier = [fuel] := by
  exact congrArg Snapshot.frontier (generation_run_eq fuel)

theorem generation_not_finitely_closes :
    ¬ generationScenario.FinitelyCloses := by
  exact stream_not_finitely_closes portfolioStepAuthority portfolioClaim
    portfolioExecution portfolioCodec.realize

/-- The value observer sees exactly the previously checked generated route,
not a newly reconstructed list with merely equal residents. -/
theorem observed_generation_eq_generatedPrefix (depth : Nat) :
    EventObserver.value.observeList
        (generationScenario.snapshotAt depth).events =
      generatedPrefix depth := by
  change
    EventObserver.value.observeList
        (run generationSystem Scheduler.breadthFirst depth
          (initial [0])).events = generatedPrefix depth
  rw [generation_run_eq, EventObserver.observeList_value,
    generatedPrefix_eq_range_map]
  simp

/-- The observer-visible prefix is exactly the realization of the retained
GSLT-IL route at the same demand depth. -/
theorem observed_generation_is_retained_route (depth : Nat) :
    EventObserver.value.observeList
        (generationScenario.snapshotAt depth).events =
      portfolioCodec.realizeRoute foregroundAccepting
        (retainedPortfolioPrefix depth).erase := by
  rw [observed_generation_eq_generatedPrefix,
    retainedPortfolioPrefix_realizes_generatedPrefix]

/-! ## Productive generated-work and resident streams -/

/-- Every finite demand for exact generated work is met after the same finite
number of controller epochs. -/
theorem generation_stream_productive :
    StreamProductiveFor generationScenario EventObserver.value
      generatedOccurrenceAt := by
  exact stream_productive portfolioStepAuthority portfolioClaim
    portfolioExecution portfolioCodec.realize

/-- Forgetting down to the typed resident role is a local observer map, so it
preserves stream productivity without claiming that resident identity recovers
the source occurrence. -/
def residentObserver : EventObserver Nat Occurrence Role :=
  EventObserver.value.map TriggeredOccurrence.resident

theorem resident_stream_productive :
    StreamProductiveFor generationScenario residentObserver
      (fun index => (generatedOccurrenceAt index).resident) := by
  exact generation_stream_productive.map TriggeredOccurrence.resident

/-! ## Every foreground/background role is independently productive -/

/-- Controller epochs five steps apart activate the same typed resident. -/
theorem generatedOccurrenceAt_resident_add_five (epoch : Nat) :
    (generatedOccurrenceAt (epoch + 5)).resident =
      (generatedOccurrenceAt epoch).resident := by
  change nextRole (portfolioExecution.state (epoch + 5)) =
    nextRole (portfolioExecution.state epoch)
  rw [portfolioExecution_state_add_five]

/-- The offset of one role in the authored five-step controller cycle. -/
def roleOffset : Role → Nat
  | .ecan => 0
  | .incrementalCompression => 1
  | .pln => 2
  | .premiseSelection => 3
  | .foregroundChaining => 4

/-- Repeating a cycle preserves the resident at every authored offset. -/
theorem generatedOccurrenceAt_resident_cycle_offset
    (cycle offset : Nat) :
    (generatedOccurrenceAt (5 * cycle + offset)).resident =
      (generatedOccurrenceAt offset).resident := by
  induction cycle with
  | zero => simp
  | succ cycle inductionHypothesis =>
      calc
        (generatedOccurrenceAt (5 * (cycle + 1) + offset)).resident =
            (generatedOccurrenceAt ((5 * cycle + offset) + 5)).resident := by
              apply congrArg
                (fun index => (generatedOccurrenceAt index).resident)
              omega
        _ = (generatedOccurrenceAt (5 * cycle + offset)).resident :=
          generatedOccurrenceAt_resident_add_five (5 * cycle + offset)
        _ = (generatedOccurrenceAt offset).resident := inductionHypothesis

/-- Each role has one exact, recurring slot in every controller cycle. -/
theorem generatedOccurrenceAt_role_slot (role : Role) (cycle : Nat) :
    (generatedOccurrenceAt (5 * cycle + roleOffset role)).resident = role := by
  rw [generatedOccurrenceAt_resident_cycle_offset]
  cases role <;> rfl

/-- A local observer exposes a signal exactly for occurrences of one role. -/
def roleSignalObserver (role : Role) : EventObserver Nat Occurrence Role where
  observe event :=
    if event.value.resident = role then some role else none

@[simp] theorem roleSignalObserver_accepts (role : Role) (origin : Nat)
    (occurrence : Occurrence) (resident : occurrence.resident = role) :
    (roleSignalObserver role).observe ⟨origin, occurrence⟩ = some role := by
  simp [roleSignalObserver, resident]

theorem roleSignalObserver_sound (role : Role)
    (event : Emission Nat Occurrence)
    (observed : (roleSignalObserver role).observe event = some role) :
    event.value.resident = role := by
  simpa [roleSignalObserver] using observed

/-- A different resident cannot masquerade as the requested role. -/
theorem roleSignalObserver_rejects_other
    (role other : Role) (different : other ≠ role) (origin : Nat) :
    (roleSignalObserver role).observe
        ⟨origin, { generatedAt := origin, trigger := (), resident := other }⟩ =
      none := by
  simp [roleSignalObserver, different]

/-- One complete controller block exposes exactly one signal for any selected
role.  The five resident equalities come from the checked periodic route, not
from a freshly declared scheduler table. -/
theorem roleSignalObserver_cycle_block (role : Role) (cycle : Nat) :
    (roleSignalObserver role).observeList
        ((List.range 5).map
          (fun offset =>
            ⟨5 * cycle + offset,
              generatedOccurrenceAt (5 * cycle + offset)⟩)) =
      [role] := by
  have rangeFive : List.range 5 = [0, 1, 2, 3, 4] := by decide
  have ecan :
      (generatedOccurrenceAt (5 * cycle)).resident = .ecan := by
    simpa [roleOffset] using generatedOccurrenceAt_role_slot .ecan cycle
  have compression :
      (generatedOccurrenceAt (5 * cycle + 1)).resident =
        .incrementalCompression := by
    simpa [roleOffset] using
      generatedOccurrenceAt_role_slot .incrementalCompression cycle
  have pln :
      (generatedOccurrenceAt (5 * cycle + 2)).resident = .pln := by
    simpa [roleOffset] using generatedOccurrenceAt_role_slot .pln cycle
  have premise :
      (generatedOccurrenceAt (5 * cycle + 3)).resident =
        .premiseSelection := by
    simpa [roleOffset] using
      generatedOccurrenceAt_role_slot .premiseSelection cycle
  have foreground :
      (generatedOccurrenceAt (5 * cycle + 4)).resident =
        .foregroundChaining := by
    simpa [roleOffset] using
      generatedOccurrenceAt_role_slot .foregroundChaining cycle
  rw [rangeFive]
  simp only [List.map_cons, List.map_nil, EventObserver.observeList,
    List.filterMap_cons, List.filterMap_nil]
  cases role <;>
    simp [roleSignalObserver, ecan, compression,
      pln, premise, foreground]

/-- Filtering the first `cycles` complete controller rounds for any one role
returns exactly one signal per round. -/
theorem roleSignalObserver_range_cycles (role : Role) (cycles : Nat) :
    (roleSignalObserver role).observeList
        ((List.range (5 * cycles)).map
          (fun index => ⟨index, generatedOccurrenceAt index⟩)) =
      List.replicate cycles role := by
  induction cycles with
  | zero => simp [EventObserver.observeList]
  | succ cycles inductionHypothesis =>
      rw [show 5 * (cycles + 1) = 5 * cycles + 5 by omega,
        List.range_add, List.map_append,
        EventObserver.observeList_append, inductionHypothesis,
        List.replicate_succ']
      rw [show
        (roleSignalObserver role).observeList
            (List.map (fun index =>
              { origin := index, value := generatedOccurrenceAt index })
              (List.map (fun x => 5 * cycles + x) (List.range 5))) =
          [role] by
        simpa [List.map_map, Function.comp_def] using
          roleSignalObserver_cycle_block role cycles]

/-- The actual generated scenario exposes one occurrence of the selected role
per completed five-step controller round. -/
theorem roleSignalObserver_observed_cycles (role : Role) (cycles : Nat) :
    (roleSignalObserver role).observeList
        (generationScenario.snapshotAt (5 * cycles)).events =
      List.replicate cycles role := by
  change
    (roleSignalObserver role).observeList
        (run generationSystem Scheduler.breadthFirst (5 * cycles)
          (initial [0])).events = List.replicate cycles role
  rw [generation_run_eq]
  exact roleSignalObserver_range_cycles role cycles

/-- No foreground or background role can disappear behind productive output
from the other roles: every finite role-specific demand is met after five
times that much controller fuel. -/
theorem every_role_stream_productive (role : Role) :
    StreamProductiveFor generationScenario (roleSignalObserver role)
      (fun _ => role) := by
  intro demand
  refine ⟨5 * demand, ?_⟩
  rw [streamPrefix_const, roleSignalObserver_observed_cycles]

/-- The mixed ecology therefore supplies five independent productive views,
not merely one productive aggregate stream. -/
theorem all_five_roles_stream_productive :
    (∀ role : Role,
      StreamProductiveFor generationScenario (roleSignalObserver role)
        (fun _ => role)) :=
  every_role_stream_productive

/-! ### Exact recurring premise-service control receipts on the stream -/

/-- The premise-service occurrence used by the richer receipt layer is
definitionally the occurrence at the corresponding retained-route epoch. -/
theorem generatedOccurrenceAt_schedulerEpoch_eq_premiseOccurrence
    (cycle : Nat) :
    generatedOccurrenceAt (schedulerEpoch cycle) =
      portfolioPremiseOccurrence cycle := by
  rfl

/-- Every recurring premise-service receipt is attached to an occurrence
which appears in the exact retained generated stream. -/
theorem recurringPremiseReceipt_occurs_in_stream (cycle : Nat) :
    portfolioPremiseOccurrence cycle ∈
        EventObserver.value.observeList
          (generationScenario.snapshotAt (schedulerEpoch cycle + 1)).events ∧
      Nonempty (RecurringPremiseReceipt cycle) := by
  constructor
  · rw [observed_generation_eq_generatedPrefix,
      generatedPrefix_eq_range_map,
      ← generatedOccurrenceAt_schedulerEpoch_eq_premiseOccurrence]
    apply List.mem_map.mpr
    exact ⟨schedulerEpoch cycle, List.mem_range.mpr (by omega), rfl⟩
  · exact ⟨recurringPremiseReceipt cycle⟩

/-- Premise-selection liveness and its proof-relevant control receipts coexist,
while the receipt type continues to keep value, choice, cost, funding, and
store authority in separate fields. -/
theorem premise_role_is_productive_with_recurring_control_receipts :
    StreamProductiveFor generationScenario
        (roleSignalObserver .premiseSelection)
        (fun _ => .premiseSelection) ∧
      ∀ cycle, portfolioPremiseOccurrence cycle ∈
          EventObserver.value.observeList
            (generationScenario.snapshotAt (schedulerEpoch cycle + 1)).events ∧
        Nonempty (RecurringPremiseReceipt cycle) := by
  exact ⟨every_role_stream_productive .premiseSelection,
    recurringPremiseReceipt_occurs_in_stream⟩

/-! ## Observation demand controls finite realization -/

/-- A positive finite-prefix request retains controlled activation, realizes
exactly the requested route prefix, and leaves the next epoch live. -/
theorem positive_prefix_demand_realizes_exact_retained_route
    (count : Nat) :
    dispatch
        ({ completion := .finitePrefix (count + 1), guard := none } :
          ObservationDemand Unit)
        .general .singletonOnly =
          { readout := .finitePrefix (count + 1), activation := .controlled } ∧
      EventObserver.value.observeList
          (generationScenario.snapshotAt (count + 1)).events =
        portfolioCodec.realizeRoute foregroundAccepting
          (retainedPortfolioPrefix (count + 1)).erase ∧
      (EventObserver.value.observeList
        (generationScenario.snapshotAt (count + 1)).events).length =
          count + 1 ∧
      (generationScenario.snapshotAt (count + 1)).frontier = [count + 1] := by
  refine ⟨rfl,
    observed_generation_is_retained_route (count + 1), ?_,
    generation_frontier_eq_singleton (count + 1)⟩
  rw [observed_generation_eq_generatedPrefix,
    generatedPrefix_eq_range_map]
  simp

/-- First-witness demand does not preselect a branch, while productivity
supplies the first exact generated occurrence after finite fuel. -/
theorem first_demand_is_controlled_and_observable :
    dispatch
        ({ completion := .first, guard := none } : ObservationDemand Unit)
        .general .singletonOnly =
          { readout := .first, activation := .controlled } ∧
      ∃ fuel, (streamPrefix generatedOccurrenceAt 1).IsPrefix
        (EventObserver.value.observeList
          (generationScenario.snapshotAt fuel).events) := by
  exact ⟨branching_first_remains_controlled (Guard := Unit) none,
    generation_stream_productive 1⟩

/-- Ordered-stream demand keeps the controlled frontier and uses the
independent productivity certificate for arbitrary finite pulls. -/
theorem ordered_stream_demand_is_controlled_and_productive :
    dispatch
        ({ completion := .orderedStream, guard := none } :
          ObservationDemand Unit)
        .general .singletonOnly =
          { readout := .orderedStream, activation := .controlled } ∧
      StreamProductiveFor generationScenario EventObserver.value
        generatedOccurrenceAt := by
  exact ⟨rfl, generation_stream_productive⟩

/-- A single-path activation license does not turn a productive infinite
route into a completed finite bag. -/
theorem complete_bag_single_path_still_does_not_close :
    dispatch
        ({ completion := .completeBag, guard := none } :
          ObservationDemand Unit)
        .singlePath .serializable =
          { readout := .completeBag, activation := .singlePath } ∧
      ¬ generationScenario.FinitelyCloses :=
  ⟨rfl, generation_not_finitely_closes⟩

/-- The first demanded resident cycle is the authored foreground/background
portfolio order already checked by the route realization. -/
theorem first_resident_cycle_observed :
    residentObserver.observeList
        (generationScenario.snapshotAt 5).events =
      [.ecan, .incrementalCompression, .pln, .premiseSelection,
        .foregroundChaining] := by
  rw [residentObserver, EventObserver.observeList_map,
    observed_generation_eq_generatedPrefix]
  exact first_cycle_resident_order

/-! ## Generation, selection, and fulfillment remain separate -/

/-- Every observed generated occurrence is genuine authored space work and is
selected by the independently supplied bounded selector. -/
theorem observed_generation_is_generated_and_selected
    (depth : Nat) {occurrence : Occurrence}
    (member : occurrence ∈
      EventObserver.value.observeList
        (generationScenario.snapshotAt depth).events) :
    serviceSpace.Generated heartbeatTrace occurrence.generatedAt occurrence ∧
      ∃ offset, offset < 1 ∧
        selectedGenerated (occurrence.generatedAt + offset) occurrence := by
  rw [observed_generation_eq_generatedPrefix] at member
  constructor
  · exact portfolioCodec.mem_realizeRoute_generated foregroundAccepting
      (checkedPrefix depth) member
  · exact generatedPrefix_member_selected depth member

/-- Productive route generation still cannot make a hostile scheduler select
even the first genuine generated occurrence. -/
theorem generation_productivity_does_not_mint_hostile_selection :
    StreamProductiveFor generationScenario EventObserver.value
        generatedOccurrenceAt ∧
      (let routeOccurrence := occurrenceAt portfolioStepAuthority
          portfolioClaim portfolioExecution 0
       let generated := portfolioCodec.realize routeOccurrence
       serviceSpace.Generated heartbeatTrace generated.generatedAt generated ∧
         ¬ ∃ cycle, neverSelected cycle generated) :=
  ⟨generation_stream_productive, generation_does_not_imply_selection⟩

/-- The connected positive boundary: recurrent controller meaning, exact
route-stream productivity, the authored first role cycle, and pointwise
generated-work selection coexist as separately proved facts. -/
theorem recurrent_portfolio_has_productive_selected_route_stream :
    portfolioClaim.Meaning foregroundAccepting ∧
      StreamProductiveFor generationScenario EventObserver.value
        generatedOccurrenceAt ∧
      residentObserver.observeList
          (generationScenario.snapshotAt 5).events =
        [.ecan, .incrementalCompression, .pln, .premiseSelection,
          .foregroundChaining] ∧
      (∀ depth occurrence,
        occurrence ∈ EventObserver.value.observeList
            (generationScenario.snapshotAt depth).events →
          serviceSpace.Generated heartbeatTrace occurrence.generatedAt
              occurrence ∧
            ∃ offset, offset < 1 ∧
              selectedGenerated (occurrence.generatedAt + offset)
                occurrence) := by
  exact ⟨portfolio_checked_consequences.2, generation_stream_productive,
    first_resident_cycle_observed,
    observed_generation_is_generated_and_selected⟩

#print axioms generatedPrefix_eq_range_map
#print axioms generation_run_eq
#print axioms generation_not_finitely_closes
#print axioms observed_generation_is_retained_route
#print axioms generation_stream_productive
#print axioms resident_stream_productive
#print axioms generatedOccurrenceAt_resident_add_five
#print axioms generatedOccurrenceAt_role_slot
#print axioms roleSignalObserver_sound
#print axioms roleSignalObserver_rejects_other
#print axioms roleSignalObserver_observed_cycles
#print axioms every_role_stream_productive
#print axioms all_five_roles_stream_productive
#print axioms recurringPremiseReceipt_occurs_in_stream
#print axioms premise_role_is_productive_with_recurring_control_receipts
#print axioms positive_prefix_demand_realizes_exact_retained_route
#print axioms first_demand_is_controlled_and_observable
#print axioms ordered_stream_demand_is_controlled_and_productive
#print axioms complete_bag_single_path_still_does_not_close
#print axioms first_resident_cycle_observed
#print axioms observed_generation_is_generated_and_selected
#print axioms generation_productivity_does_not_mint_hostile_selection
#print axioms recurrent_portfolio_has_productive_selected_route_stream

end

end Mettapedia.CognitiveArchitecture.RecurrentMindAgentStreamProductivity
