import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathModelRestriction

/-!
# Actual producer outputs become shared captures; retained schemas keep private locals

The row interface follows the original computed output and capture maps.
Future opening of a shared row does not freshen producer identities. Retained
schemas still open their own locals at each use. Physical survival is stated
separately from the total row-metadata function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local O : Type} (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}

namespace Endpoint

variable {locals}

theorem row_map_equality {first second : Endpoint locals O Γ sort} (same : first = second) (occurrence : O) :
    (first.inventory.rows occurrence).map locals (equalityExtension same).assignment = second.inventory.rows occurrence := by
  cases same
  change (first.inventory.rows occurrence).map locals (generator first.declarations) = first.inventory.rows occurrence
  exact ContextualStoredRows.Row.map_identity locals _

end Endpoint

variable [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace Firing

variable {locals} {before after : Endpoint locals O Γ sort}

def outputAssignment (firing : Firing locals before after) :
    Assignment (ContextualActivatedStep.target locals before.declarations) after.declarations :=
  Assignment.compose (Endpoint.equalityExtension firing.destination.symm).assignment
    (ContextualComputedFreshFrame.includeSource firing.update)

private def relocation (firing : Firing locals before after) :
    Assignment (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals before.declarations)
      firing.update.declaration) after.declarations :=
  (Endpoint.equalityExtension firing.destination.symm).assignment

private theorem row_from_computed (firing : Firing locals before after) (occurrence : O) :
    after.inventory.rows occurrence =
      ((computedTarget locals before firing.rule firing.selection firing.outputs firing.ruleCovered
        firing.admitted firing.update).inventory.rows occurrence).map locals firing.relocation :=
  (Endpoint.row_map_equality firing.destination.symm occurrence).symm

theorem produced_row_is_shared (firing : Firing locals before after) {occurrence : O}
    (made : occurrence ∈ firing.selection.made) :
    after.inventory.rows occurrence =
      .shared (instantiate firing.outputAssignment (firing.outputs occurrence)) := by
  rw [firing.row_from_computed occurrence]
  have produced := ContextualTransportedActivation.produced_row_is_shared locals before.declarations
    (ContextualComputedFreshFrame.includeSource firing.update) firing.selection firing.outputs before.inventory.rows made
  change ((ContextualTransportedActivation.resultRows locals before.declarations
    (ContextualComputedFreshFrame.includeSource firing.update) firing.selection firing.outputs before.inventory.rows)
      occurrence).map locals firing.relocation = _
  rw [produced]
  change ContextualStoredRows.Row.shared
      (instantiate firing.relocation (instantiate (ContextualComputedFreshFrame.includeSource firing.update)
        (firing.outputs occurrence))) = _
  exact congrArg ContextualStoredRows.Row.shared (Assignment.instantiate_compose _ _ _).symm

theorem produced_row_is_present (firing : Firing locals before after) {occurrence : O}
    (made : occurrence ∈ firing.selection.made) : occurrence ∈ after.inventory.configuration.present := by
  rw [firing.physical_result]
  exact made_subset_fire (by simpa only [Selection.commit, List.mem_toFinset] using made)

theorem retained_row_map (firing : Firing locals before after) {occurrence : O}
    (old : occurrence ∈ before.inventory.configuration.present) :
    after.inventory.rows occurrence = (before.inventory.rows occurrence).map locals
      (pathAssignment (Quiver.Hom.toPath firing)) := by
  have notMade : occurrence ∉ firing.selection.made := by
    intro made
    exact Finset.disjoint_left.mp firing.admitted.occurrences.fresh
      (by simpa only [Selection.commit, List.mem_toFinset] using made) old
  rw [firing.row_from_computed occurrence]
  have retained := ContextualTransportedActivation.retained_row_keeps_private_locals locals before.declarations
    (ContextualComputedFreshFrame.includeSource firing.update) firing.selection firing.outputs before.inventory.rows notMade
  change ((ContextualTransportedActivation.resultRows locals before.declarations
    (ContextualComputedFreshFrame.includeSource firing.update) firing.selection firing.outputs before.inventory.rows)
      occurrence).map locals firing.relocation = _
  rw [retained, ContextualStoredRows.Row.map_compose]
  have captureMap := firing.captureAssignment_split
  change pathAssignment (Quiver.Hom.toPath firing) =
    Assignment.compose firing.relocation (Assignment.compose (ContextualComputedFreshFrame.includeSource firing.update)
      (ContextualSelectionViews.capturedTarget locals before.declarations)) at captureMap
  exact congrArg (fun change => (before.inventory.rows occurrence).map locals change) captureMap.symm

theorem old_untaken_row_survives (firing : Firing locals before after) {occurrence : O}
    (old : occurrence ∈ before.inventory.configuration.present) (untaken : occurrence ∉ firing.selection.taken) :
    occurrence ∈ after.inventory.configuration.present := by
  rw [firing.physical_result]
  apply mem_fire.mpr
  exact Or.inl ⟨old, by simpa only [Selection.commit, List.mem_toFinset] using untaken⟩

theorem produced_shared_views_keep_the_producer_identities (firing : Firing locals before after) {occurrence : O}
    (made : occurrence ∈ firing.selection.made) (futureScope : Nat) :
    ContextualStoredRows.viewAt locals after.declarations futureScope (after.inventory.rows occurrence) =
      instantiate (ContextualSelectionViews.capturedTarget locals after.declarations)
        (instantiate firing.outputAssignment (firing.outputs occurrence)) := by
  rw [firing.produced_row_is_shared made]
  rfl

theorem produced_shared_views_agree_at_any_two_future_scopes (firing : Firing locals before after) {occurrence : O}
    (made : occurrence ∈ firing.selection.made) (first second : Nat) :
    ContextualStoredRows.viewAt locals after.declarations first (after.inventory.rows occurrence) =
      ContextualStoredRows.viewAt locals after.declarations second (after.inventory.rows occurrence) :=
  (firing.produced_shared_views_keep_the_producer_identities made first).trans
    (firing.produced_shared_views_keep_the_producer_identities made second).symm

theorem retained_schema_uses_only_shared_names_between_fresh_views (firing : Firing locals before after)
    {occurrence : O} (old : occurrence ∈ before.inventory.configuration.present)
    (body : Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)
    (schematic : before.inventory.rows occurrence = .schema body)
    {first second : Nat} (different : first ≠ second) (name : ScopedVar Local ⊕ after.Names)
    (inFirst : name ∈ support (ContextualStoredRows.viewAt locals after.declarations first (after.inventory.rows occurrence)))
    (inSecond : name ∈ support (ContextualStoredRows.viewAt locals after.declarations second (after.inventory.rows occurrence))) :
    ∃ captured : after.Names, name = .inr captured := by
  rw [firing.retained_row_map old, schematic] at inFirst inSecond
  exact ContextualFreshening.different_activations_only_share_captures locals after.declarations different _ _ name
    inFirst inSecond

end Firing
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecution
