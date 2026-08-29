import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mettapedia.Languages.ProcessCalculi.MORK.GSLTSemantics

/-!
# Proof-relevant MM2 work-queue events

The MM2 GSLT records the graph of the deterministic work-queue step.  A
compiler also needs the selected directive as occurrence evidence, both to
relate a source action to the emitted rule that implements it and to prevent a
target scheduler from inventing a different event with the same endpoint.

This module equips the existing open-world MM2 execution profile with exactly
that evidence.  It introduces neither a new MM2 dialect nor an intermediate
runtime language.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.ProofRelevantGSLT

open Mettapedia.GSLT.ProofRelevant
open Mettapedia.Languages.ProcessCalculi.MORK

/-- One selected, supported MM2 directive and its exact computed successor. -/
structure ScheduledEvent (source target : Space) : Type where
  directive : SourceExecFact
  selected :
    selectNextScheduled (supportedSourceExecFactsOfSpace source) =
      some directive
  fired : fireSourceExecFact source directive = target

/-- Supported open-world MM2 execution has exactly the scheduled-event
occurrences above. -/
theorem scheduledEvent_nonempty_iff_step (source target : Space) :
    Nonempty (ScheduledEvent source target) ↔
      (sourceExecGSLT .leaveInert).Step source target := by
  rw [sourceExecGSLT_step_iff]
  constructor
  · rintro ⟨event⟩
    simp [sourceWorkQueueStep, event.selected, event.fired]
  · intro step
    unfold sourceWorkQueueStep at step
    cases selected :
        selectNextScheduled (supportedSourceExecFactsOfSpace source) with
    | none =>
        simp [selected] at step
    | some directive =>
        simp [selected] at step
        exact ⟨⟨directive, selected, step⟩⟩

/-- Exact step evidence for the existing ordinary MM2 language profile used
by source-to-MM2 compilers. -/
noncomputable def stepEvidence :
    StepEvidence (sourceExecGSLT .leaveInert) where
  Evidence := ScheduledEvent
  erases_iff := scheduledEvent_nonempty_iff_step

noncomputable def system : ProofRelevantGSLT :=
  { theory := sourceExecGSLT .leaveInert
    steps := stepEvidence }

/-! ## Boundary controls -/

/-- Every explicitly selected supported directive yields its retained target
event. -/
def eventOfSelected {source : Space} {directive : SourceExecFact}
    (selected :
      selectNextScheduled (supportedSourceExecFactsOfSpace source) =
        some directive) :
    ScheduledEvent source (fireSourceExecFact source directive) :=
  { directive
    selected
    fired := rfl }

/-- No scheduled event exists when the supported work queue is empty. -/
theorem no_event_of_no_supported
    {source target : Space}
    (empty :
      selectNextScheduled (supportedSourceExecFactsOfSpace source) = none) :
    IsEmpty (ScheduledEvent source target) := by
  constructor
  intro event
  have selected := event.selected
  rw [empty] at selected
  contradiction

#print axioms scheduledEvent_nonempty_iff_step
#print axioms no_event_of_no_supported

end Mettapedia.Languages.ProcessCalculi.MORK.ProofRelevantGSLT
