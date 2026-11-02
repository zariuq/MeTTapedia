import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceProcess

/-!
# Actual contextual schedules project to the resource operators

This projection forgets terms and equations but preserves occurrence identity,
every repeated read port, each original pre-event world and the complete final
physical world. No guard acceptance is needed to validate the prepared data's
resource projection. Reordering this projection alone is not a theorem that
the contextual activations or their guard cuts may be reordered.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}

theorem resource_runs_append (first second : List (List O × List O × List O)) :
    ResourceOccupation.runs (first ++ second) =
      ResourceOccupation.andThen (ResourceOccupation.runs first) (ResourceOccupation.runs second) := by
  induction first with
  | nil => rfl
  | cons event rest earlier =>
      simp only [List.cons_append, ResourceOccupation.runs, earlier,
        ResourceOccupation.andThen_assoc]

theorem prepared_resource_result {before : Endpoint locals O Γ sort} (prepared : Prepared locals before) :
    ResourceOccupation.commit prepared.selection.taken prepared.selection.read prepared.selection.made
      before.inventory.configuration.present = some prepared.target.inventory.configuration.present := by
  have source := (ContextualInteractionFactors.resources_iff prepared.outputs prepared.selection
    before.inventory.configuration.present).mp prepared.resources
  exact ResourceOccupation.commit_eq_fire prepared.outputs prepared.selection before.inventory.configuration.present
    source.1 source.2.1 source.2.2

theorem certificate_resource_word {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) :
    ResourceOccupation.runs (certificate.selections.map ResourceProcess.ports)
      source.inventory.configuration.present = some target.inventory.configuration.present := by
  induction certificate with
  | nil => rfl
  | snoc past next earlier =>
      simp only [Certificate.selections, List.map_append, List.map_cons, List.map_nil, resource_runs_append]
      change (ResourceOccupation.runs (past.selections.map ResourceProcess.ports)
        source.inventory.configuration.present).bind _ = _
      rw [earlier, Option.bind_some]
      change (ResourceOccupation.commit next.selection.taken next.selection.read next.selection.made
        _).bind ResourceOccupation.one = _
      rw [prepared_resource_result]
      rfl

theorem catalogue_resource_word {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) :
    ResourceOccupation.runs ((events certificate).map (fun event => ResourceProcess.ports event.selection))
      source.inventory.configuration.present = some target.inventory.configuration.present := by
  have same := congrArg (List.map ResourceProcess.ports) (selections_preserved certificate)
  simp only [List.map_map, Function.comp_def] at same
  rw [same]
  exact certificate_resource_word certificate

theorem every_original_world_admits_its_resource_selection {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) :
    ∀ event ∈ events certificate,
      ContextualInteractionFactors.Resources event.selection event.guardWorld := by
  induction certificate with
  | nil => intro event member; cases member
  | snoc past next earlier =>
      intro event member
      rcases List.mem_append.mp member with prior | last
      · obtain ⟨original, present, rfl⟩ := List.mem_map.mp prior
        exact earlier original present
      · obtain rfl := List.mem_singleton.mp last
        exact next.resources

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue
