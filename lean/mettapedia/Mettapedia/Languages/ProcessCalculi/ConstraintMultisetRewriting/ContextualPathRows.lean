import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRowOrigins

/-!
# Persistent physical rows transport along actual contextual paths

An originally present occurrence that is never consumed remains present.
Fresh-output admission then prevents reusing its identity, and its original
schema/shared metadata follows the pure composed capture inclusion. Consumed
and later reused identities are deliberately outside this theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}

def NeverTaken {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target) (occurrence : O) : Prop :=
  ∀ selection ∈ selections path, occurrence ∉ selection.taken

theorem persistent_row_along_path {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target)
    {occurrence : O} (present : occurrence ∈ source.inventory.configuration.present) (untaken : NeverTaken path occurrence) :
    occurrence ∈ target.inventory.configuration.present ∧
      target.inventory.rows occurrence = (source.inventory.rows occurrence).map locals (pathAssignment path) := by
  induction path with
  | nil => exact ⟨present, (ContextualStoredRows.Row.map_identity locals _).symm⟩
  | cons past edge earlier =>
      have prefixUntaken : NeverTaken past occurrence :=
        fun selection member => untaken selection (List.mem_append_left _ member)
      have lastUntaken : occurrence ∉ edge.selection.taken :=
        untaken edge.selection (List.mem_append_right _ (List.mem_singleton_self _))
      have prefixRow := earlier prefixUntaken
      refine ⟨edge.old_untaken_row_survives prefixRow.1 lastUntaken, ?_⟩
      rw [edge.retained_row_map prefixRow.1, prefixRow.2, ContextualStoredRows.Row.map_compose]
      change (source.inventory.rows occurrence).map locals
          (Assignment.compose (pathAssignment (Quiver.Hom.toPath edge)) (pathAssignment past)) =
        (source.inventory.rows occurrence).map locals (pathAssignment (past.comp (Quiver.Hom.toPath edge)))
      exact congrArg (fun change => (source.inventory.rows occurrence).map locals change)
        (pathAssignment_comp past (Quiver.Hom.toPath edge)).symm

theorem persistent_shared_views_keep_shared_values {source target : Endpoint locals O Γ sort}
    (path : Quiver.Path source target) {occurrence : O}
    (present : occurrence ∈ source.inventory.configuration.present) (untaken : NeverTaken path occurrence)
    (value : Term (signature S source.declarations) Γ sort)
    (isShared : source.inventory.rows occurrence = .shared value) (futureScope : Nat) :
    occurrence ∈ target.inventory.configuration.present ∧
      ContextualStoredRows.viewAt locals target.declarations futureScope (target.inventory.rows occurrence) =
        instantiate (ContextualSelectionViews.capturedTarget locals target.declarations)
          (instantiate (pathAssignment path) value) := by
  have transported := persistent_row_along_path path present untaken
  refine ⟨transported.1, ?_⟩
  rw [transported.2, isShared]
  rfl

theorem persistent_schema_views_only_share_captures {source target : Endpoint locals O Γ sort}
    (path : Quiver.Path source target) {occurrence : O}
    (present : occurrence ∈ source.inventory.configuration.present) (untaken : NeverTaken path occurrence)
    (body : Term (signature S (ContextualActivatedStep.source locals source.declarations)) Γ sort)
    (schematic : source.inventory.rows occurrence = .schema body)
    {first second : Nat} (different : first ≠ second) (name : ScopedVar Local ⊕ target.Names)
    (inFirst : name ∈ support (ContextualStoredRows.viewAt locals target.declarations first (target.inventory.rows occurrence)))
    (inSecond : name ∈ support (ContextualStoredRows.viewAt locals target.declarations second (target.inventory.rows occurrence))) :
    ∃ captured : target.Names, name = .inr captured := by
  have transported := (persistent_row_along_path path present untaken).2
  rw [transported, schematic] at inFirst inSecond
  exact ContextualFreshening.different_activations_only_share_captures locals target.declarations different _ _ name
    inFirst inSecond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecution
