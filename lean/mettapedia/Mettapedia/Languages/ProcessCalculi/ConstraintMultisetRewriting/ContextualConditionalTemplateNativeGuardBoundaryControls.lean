import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeGuardControls

/-!
# Binding and result equivalence do not establish guard admission

A private prefix creates a row that refutes a later absence query. The
source body is refused, but its binding/resource producer still executes.
The complete compiler must attach the original-cut data queries before
claiming an admission comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeGuardBoundaryControls

open ContextualConditionalTemplateSchedules
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

abbrev source := Schedule.segment
  (Schedule.nil ContextualPrefixPublicationControls.initial) ContextualNativeGuardControls.Virtual.body

theorem source_guard_refuses : ¬ source.Admitted :=
  fun admitted => ContextualNativeGuardControls.Virtual.source_guard_refuses_the_internal_creation admitted.2

theorem source_shapes : source.ShapesHold := by
  apply (Schedule.shapes_segment _ _).mpr
  exact ⟨(fun _ member => by cases member), ContextualNativeGuardControls.Virtual.shapes⟩

theorem source_resources : Executable ContextualSourceSchedules.Schedule.unitLabel
    ContextualPrefixPublicationControls.initial.present source.commits := by
  exact ContextualNativeGuardControls.Virtual.resources

theorem the_binding_producer_still_executes (occupied : Finset Nat) (fuel : Nat) :
    ∃ publication : source.NativePublication occupied, publication.firing.fuel = fuel :=
  source.realize_native_publication source_shapes source_resources
    ContextualNativeGuardControls.Virtual.consistent occupied fuel

theorem producer_existence_cannot_replace_source_admission :
    ¬ (source.Admitted ↔ Nonempty (source.NativePublication ∅)) := by
  intro comparison
  obtain ⟨publication, _budget⟩ := the_binding_producer_still_executes ∅ 0
  exact source_guard_refuses (comparison.mpr ⟨publication⟩)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeGuardBoundaryControls
