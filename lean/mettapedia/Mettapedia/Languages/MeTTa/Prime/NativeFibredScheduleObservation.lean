import Mettapedia.GSLT.LanguageDef.CostScheduleObservation
import Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture
import Mettapedia.Languages.MeTTa.Prime.NativeCostOneOperationalAdequacy

/-!
# Prime fibred schedules as capability-indexed observations

Prime's separation and colouring certificates compile to proof-relevant Cost
schedules before any observation is taken.  The generic schedule observation
then recovers WorkSpan while retaining exact wave events and occurrence
receipts.  This module proves that the pairwise, finite-family, and finite-wave
Prime constructions all cross that boundary without loss of their declared
indices.

The negative control is equally important: an inhabitant of the WorkSpan
value type, including the desirable value `(2, 1)`, cannot create a separation
certificate for a contested resource.  Values observe licensed execution;
they do not authorize it.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeFibredScheduleObservation

open Mettapedia.Algebra
open Mettapedia.GSLT.LanguageDef.CostOneOperationalAdequacy
open Mettapedia.GSLT.LanguageDef.CostScheduleObservation
open Mettapedia.Languages.MeTTa.Prime.NativeCostOneOperationalAdequacy
open Mettapedia.Languages.MeTTa.Prime.NativeFibredCost
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-! ## Prime schedules inhabit the public observation architecture -/

/-- Prime's proof-relevant operational schedules, retained wave events,
WorkSpan valuation, and reachable observation domain as one instance of the
generic capability-indexed architecture. -/
def scheduleArchitecture (Ground : Type u) :
    Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture
      (CostConfig Ground)
      (Mettapedia.GSLT.LanguageDef.CostOneOperationalAdequacy.OperationalSchedule
        Ground) where
  Event := WaveEvent Ground
  discipline := Schedule.discipline Ground
  observation := Schedule.observation Ground
  domain :=
    Mettapedia.GSLT.Dynamics.ObservationDiscipline.OperationalDomain.reachable
      (Schedule.discipline Ground)

/-- A scheduler view that sees work but not critical-path span. -/
def workScheduler (Ground : Type u) :
    (scheduleArchitecture Ground).SchedulerReadout Nat where
  readout := WorkSpan.work

/-- Work-only scheduling is policy-specific: it exactly supports work-based
maximum selection on every observed Prime schedule. -/
theorem workScheduler_supports_workSelection (Ground : Type u) :
    (workScheduler Ground).SupportsMaxSelection WorkSpan.work := by
  rw [Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture.SchedulerReadout.supportsMaxSelection_iff_constantOnReadoutFibers]
  intro first second firstMember secondMember sameWork
  exact sameWork

/-- The work scheduler is genuinely lossy as a readout of WorkSpan. -/
theorem workScheduler_isLossy (Ground : Type u) :
    (workScheduler Ground).Lossy := by
  apply
    Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture.SchedulerReadout.lossy_of_collision
      (workScheduler Ground)
      (first := (⟨2, 1⟩ : WorkSpan)) (second := ⟨2, 2⟩)
  · intro same
    have sameSpan := congrArg WorkSpan.span same
    norm_num at sameSpan
  · rfl

/-- Pairwise Prime separation is observed as the licensed parallel value. -/
@[simp] theorem pair_observed_workSpan {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    (Schedule.observation Ground).value
        (compiledOperationalSchedule separation) = ⟨2, 1⟩ := by
  rw [Schedule.observed_value, compiled_workSpan]

/-- The observation boundary retains the pair's complete occurrence receipt. -/
@[simp] theorem pair_observed_receipt {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    Schedule.eventReceipt
        (Schedule.events (compiledOperationalSchedule separation)) =
      separation.receipt := by
  rw [Schedule.eventReceipt_events, compiled_receipt]

/-- A separated finite family is observed as one wave whose work is its exact
number of event occurrences. -/
@[simp] theorem family_observed_workSpan {Ground : Type u}
    {events : List (CostedEvent Ground)} {source : CostConfig Ground}
    (separation : FamilySeparation Ground events source) :
    (Schedule.observation Ground).value
        (familyOperationalSchedule separation) = ⟨events.length, 1⟩ := by
  rw [Schedule.observed_value, family_workSpan]

/-- Finite-family observation retains its complete funded-occurrence receipt. -/
@[simp] theorem family_observed_receipt {Ground : Type u}
    {events : List (CostedEvent Ground)} {source : CostConfig Ground}
    (separation : FamilySeparation Ground events source) :
    Schedule.eventReceipt
        (Schedule.events (familyOperationalSchedule separation)) =
      separation.receipt := by
  unfold familyOperationalSchedule
  exact Schedule.observed_receipt_ofIndexed separation.schedule

/-- The finite-family bridge simultaneously preserves positional occurrence
identity, the exact receipt, and the declared WorkSpan value. -/
theorem family_observation_adequacy {Ground : Type u}
    {events : List (CostedEvent Ground)} {source : CostConfig Ground}
    (separation : FamilySeparation Ground events source) :
    (∀ index : Fin events.length,
        separation.occurrenceIndices.count index = 1) ∧
      Schedule.eventReceipt
          (Schedule.events (familyOperationalSchedule separation)) =
        separation.receipt ∧
      (Schedule.observation Ground).value
          (familyOperationalSchedule separation) = ⟨events.length, 1⟩ :=
  ⟨separation.occurrence_index_count_eq_one,
    family_observed_receipt separation,
    family_observed_workSpan separation⟩

/-- Any valid finite colouring is observed with work equal to the flattened
occurrence count. -/
@[simp] theorem coloring_observed_work {Ground : Type u}
    {source target : CostConfig Ground}
    {waves : List (List (CostedEvent Ground))}
    (coloring : ValidWaveColoring Ground source waves target) :
    ((Schedule.observation Ground).value
      (coloringOperationalSchedule coloring)).work = waves.flatten.length := by
  rw [Schedule.observed_value, coloring_work]

/-- Any valid finite colouring is observed with span equal to its number of
supplied colour classes; no minimal-colouring claim is made. -/
@[simp] theorem coloring_observed_span {Ground : Type u}
    {source target : CostConfig Ground}
    {waves : List (List (CostedEvent Ground))}
    (coloring : ValidWaveColoring Ground source waves target) :
    ((Schedule.observation Ground).value
      (coloringOperationalSchedule coloring)).span = waves.length := by
  rw [Schedule.observed_value, coloring_span]

/-- Strengthening a conflict analysis while retaining the same certified
colouring cannot change its observation. -/
theorem separation_refinement_preserves_observation {Ground : Type u}
    {events : List (CostedEvent Ground)} {source target : CostConfig Ground}
    (coloring : ValidConflictColoring Ground events source target)
    (stronger : OccurrenceConflictGraph events.length)
    (refines : stronger.SeparationRefines coloring.graph) :
    (coloring.ofSeparationRefines stronger refines).toSchedule.workSpan =
      coloring.toSchedule.workSpan := by
  apply WorkSpan.ext
  · rw [(coloring.ofSeparationRefines stronger refines).work_eq_event_count,
      coloring.work_eq_event_count]
  · exact coloring.span_ofSeparationRefines stronger refines

namespace Examples

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration.Examples

/-- Repeated equal event values remain three positional occurrences while the
one-wave observation reports `(3, 1)`. -/
theorem repeated_family_observation_retains_occurrences :
    repeatedFamily.occurrenceIndices.count (2 : Fin 3) = 1 ∧
      (Schedule.observation Ground).value
        (familyOperationalSchedule repeatedFamily) = ⟨3, 1⟩ :=
  ⟨repeated_family_occurrence_two_once,
    family_observed_workSpan repeatedFamily⟩

/-- The one-colour and two-colour realizations preserve identical work while
the observed span records the authorized scheduling difference. -/
theorem separation_changes_span_not_work :
    (Schedule.observation Ground).value
          (familyOperationalSchedule oneColourFamily) = ⟨2, 1⟩ ∧
      (Schedule.observation Ground).value
          (coloringOperationalSchedule twoColouring) = ⟨2, 2⟩ := by
  constructor
  · exact family_observed_workSpan oneColourFamily
  · apply WorkSpan.ext
    · exact coloring_observed_work twoColouring
    · exact coloring_observed_span twoColouring

/-- Both the one-wave and two-wave schedules are executable members of the
same declared domain.  Their equal work scores therefore cannot support a
span-maximizing policy through the work-only scheduler view. -/
theorem workScheduler_not_supports_spanSelection :
    ¬ (workScheduler Ground).SupportsMaxSelection WorkSpan.span := by
  rw [Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture.SchedulerReadout.supportsMaxSelection_iff_constantOnReadoutFibers]
  intro constant
  have oneMember :=
    (scheduleArchitecture Ground).observed_container_mem
      (familyOperationalSchedule oneColourFamily)
  have twoMember :=
    (scheduleArchitecture Ground).observed_container_mem
      (coloringOperationalSchedule twoColouring)
  have oneValue :
      (scheduleArchitecture Ground).observation.container
          (familyOperationalSchedule oneColourFamily) = ⟨2, 1⟩ := by
    exact family_observed_workSpan oneColourFamily
  have twoValue :
      (scheduleArchitecture Ground).observation.container
          (coloringOperationalSchedule twoColouring) = ⟨2, 2⟩ := by
    exact separation_changes_span_not_work.2
  rw [oneValue] at oneMember
  rw [twoValue] at twoMember
  have impossible := constant oneMember twoMember rfl
  norm_num at impossible

/-- The desirable parallel value exists independently of whether the
contested execution has a separation proof.  A value cannot mint authority. -/
theorem parallel_value_does_not_mint_contested_separation :
    Nonempty { value : WorkSpan // value = ⟨2, 1⟩ } ∧
      ¬ Nonempty
        (CostEffectSeparation Ground contestedSource leftEvent leftCompetitor) :=
  by
    constructor
    · exact ⟨⟨⟨2, 1⟩, rfl⟩⟩
    · rintro ⟨separation⟩
      exact contested_has_no_parallel_separation separation

/-- The executable analyzer therefore exposes no observed schedule for the
contested pair. -/
theorem contested_has_no_observed_schedule :
    analyzeOperational? contestedSource leftEvent leftCompetitor = none :=
  NativeCostOneOperationalAdequacy.Examples.contested_operational_analysis_is_none

end Examples

#print axioms pair_observed_workSpan
#print axioms scheduleArchitecture
#print axioms workScheduler_supports_workSelection
#print axioms workScheduler_isLossy
#print axioms pair_observed_receipt
#print axioms family_observation_adequacy
#print axioms coloring_observed_work
#print axioms coloring_observed_span
#print axioms separation_refinement_preserves_observation
#print axioms Examples.repeated_family_observation_retains_occurrences
#print axioms Examples.separation_changes_span_not_work
#print axioms Examples.workScheduler_not_supports_spanSelection
#print axioms Examples.parallel_value_does_not_mint_contested_separation
#print axioms Examples.contested_has_no_observed_schedule

end Mettapedia.Languages.MeTTa.Prime.NativeFibredScheduleObservation
