import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementLabels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentRunControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementControls

/-!
# Occurrence provenance in dependent run comparisons

The actual helper transport fixes physical occurrence identities. Therefore
its complete take/read/make selection is an event observation, and follows
the event bijection through every composed comparison. An arbitrary rule
label need not be such an observation: the existing publication control
deliberately admits alike firings with different Boolean labels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  (levels : LevelModel rules L) (O : Type) [DecidableEq O]

noncomputable def occurrenceObservation :
    (helperTransport levels O).EventObservation (Selection O) where
  label firing := firing.toFiring.selection
  moving _ firing := Natural.selection_move _ firing.data
  alikeness alike := helper_selection_alike alike
  residual _ _ second := Natural.selection_move _ second.data

theorem occurrences_follow_events {start : State rules O}
    {first second : (helperStep levels O).toStep.Run start}
    (cell : Transport.RunRearrangement.Cell (helperTransport levels O) first second)
    (event : Fin first.word.length) :
    ((occurrenceObservation levels O).labels second)[(Transport.RunRearrangement.events (helperTransport levels O) cell event).val]? =
      ((occurrenceObservation levels O).labels first)[event.val]? :=
  (occurrenceObservation levels O).labels_cell cell event

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RunRearrangementControls

open InterchangeTraceControls (T)

theorem raw_rule_label_needs_a_license :
    ¬ ∃ observation : T.EventObservation Bool,
      ∀ label : Bool, observation.label (state := EventTraceControls.start) label = label := by
  rintro ⟨observation, faithful⟩
  have same := observation.alikeness (state := EventTraceControls.start)
    (first := true) (second := false) True.intro
  rw [faithful true, faithful false] at same
  cases same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RunRearrangementControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.occurrences_follow_events
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RunRearrangementControls.raw_rule_label_needs_a_license
