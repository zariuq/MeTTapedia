import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategory
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceOccupation

/-!
# Actual kernel firings inhabit the same occurrence-resource submodel

The inference execution category is a proof observation of ordinary selected
CMR firings. Their resources are computed by the same occupation operator.
Protected theorem occurrences are retained, while each server consumes one
public request. This is a persistent resource submodel, not a claim that the
whole inference implementation has no linear resources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.LanguageDef
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload system postRule)
open InferenceSelectedFirings InferenceTraceClassifying

variable {definition : ValidatedCalculusLanguageDef} {actor : Bool}
  {before after : Configuration Value Occurrence}

theorem firing_has_resource_information_factors
    (firing : SelectedFiring definition actor before after) :
    (firing.rule.take.length = firing.picked.taken.length ∧
      firing.rule.read.length = firing.picked.read.length ∧
      firing.picked.made.map label = firing.rule.produce) ∧
    ((∃ world, ResourceOccupation.commit firing.picked.taken firing.picked.read
        firing.picked.made before.present = some world) ∧
      Disjoint firing.picked.made.toFinset firing.picked.taken.toFinset) ∧
    (locatedAction.Consistent (firing.picked.problem label firing.rule before) ∧
      ∀ check ∈ firing.rule.checks,
        locatedAction.Entails (firing.picked.problem label firing.rule before)
          (fun assignment => check.Holds locatedAction assignment label before.present)) :=
  (ResourceOccupation.valid_iff_resource_information locatedAction firing.picked label firing.rule before).mp
    firing.qualified

theorem firing_resource_operator_computes_actual_world
    (firing : SelectedFiring definition actor before after) :
    ResourceOccupation.commit firing.picked.taken firing.picked.read firing.picked.made before.present =
      some after.present := by
  exact (ResourceOccupation.valid_result_world locatedAction firing.picked label firing.rule before firing.qualified).trans
    (congrArg (fun state => some state.present) firing.destination.symm)

theorem no_protected_occurrence_is_taken (firing : SelectedFiring definition actor before after)
    (occurrence : Occurrence) (protectedHere : location occurrence = .judgments) :
    occurrence ∉ firing.picked.taken := by
  cases actor with
  | false =>
      obtain ⟨origin⟩ := firing.client_origin
      have empty : firing.picked.taken = [] := by
        apply List.length_eq_zero_iff.mp
        simpa only [origin.rule_eq, postRule, List.length_nil] using firing.qualified.take_length.symm
      simp only [empty, List.not_mem_nil, not_false_eq_true]
  | true =>
      obtain ⟨origin⟩ := firing.kernel_origin
      intro member
      have requested := origin.taken_requests occurrence member
      rw [protectedHere] at requested
      cases requested

theorem protected_occurrence_survives (firing : SelectedFiring definition actor before after)
    (occurrence : Occurrence) (present : occurrence ∈ before.present)
    (protectedHere : location occurrence = .judgments) : occurrence ∈ after.present := by
  rw [firing.destination]
  apply mem_fire.mpr
  left
  refine ⟨present, ?_⟩
  intro taken
  exact no_protected_occurrence_is_taken firing occurrence protectedHere
    (by simpa only [Selection.commit, List.mem_toFinset] using taken)

theorem trace_preserves_protected_occurrences {actors : List Bool}
    (trace : SelectedRun definition before actors after) (occurrence : Occurrence)
    (present : occurrence ∈ before.present) (protectedHere : location occurrence = .judgments) :
    occurrence ∈ after.present := by
  induction trace with
  | nil => exact present
  | cons firing rest earlier =>
      exact earlier (protected_occurrence_survives firing occurrence present protectedHere)

theorem server_still_consumes_one_request (firing : SelectedFiring definition true before after) :
    firing.picked.taken.length = 1 ∧
      ∀ occurrence ∈ firing.picked.taken, location occurrence = .requests := by
  obtain ⟨origin⟩ := firing.kernel_origin
  refine ⟨?_, origin.taken_requests⟩
  simpa only [origin.rule_eq, InferenceSchemaKernel.locate, LocatedRequest.lift,
    InferenceSchemaActivation.fromResult, List.length_map, List.length_cons, List.length_nil] using
    firing.qualified.take_length.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference
