import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotion

/-!
# Composed guarded expansion retains source and publication authority

Permission to reuse an installed macro is checked against the current source
schema inventory and every expanded edge's actual rights. These theorems
concern physical publication/consumption; protection of shared bindings is a
separate information-interface contract.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotion

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualExecution ContextualSchedulePromotion

variable {S : Signature} {Local O R N : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}
  {Inputs : Endpoint locals O Γ sort → Type}
  {activate : Activation locals Inputs (R := R)}

namespace Plan

variable {source middle target : Endpoint locals O Γ sort}

theorem permissions_append_iff (first : Plan locals Inputs activate source middle)
    (second : Plan locals Inputs activate middle target)
    (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N)) :
    (first.append second).Permissions process location sites ↔
      first.Permissions process location sites ∧ second.Permissions process location sites := by
  induction second with
  | nil => simp [append, Permissions]
  | snoc past next earlier => simp only [append, Permissions, earlier, and_assoc]

theorem ready_append_iff (first : Plan locals Inputs activate source middle)
    (second : Plan locals Inputs activate middle target)
    (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N)) :
    (first.append second).Ready process location sites ↔
      first.Ready process location sites ∧ second.Ready process location sites := by
  simp only [Ready, prerequisites_append, List.forall_mem_append, permissions_append_iff,
    erase_append, Certificate.questions_append, checked_append_iff]
  tauto

theorem missing_prerequisite_refuses (plan : Plan locals Inputs activate source target)
    (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N)) {schema : R}
    (used : schema ∈ plan.prerequisites) (uninstalled : schema ∉ process.schemas) :
    ¬ plan.Ready process location sites := fun ready => uninstalled (ready.1 schema used)

end Plan

/-- A reusable plan never gains permission to publish a missing physical
occurrence merely from having retained its derivation or its guard checks. -/
theorem licensed_path_no_new_without_send
    (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N))
    {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target)
    (licensed : LicensedPath (activate := activate) process location sites path)
    (occurrence : O) (denied : process.rights (location occurrence) .send = false)
    (present : occurrence ∈ target.inventory.configuration.present) :
    occurrence ∈ source.inventory.configuration.present := by
  induction path with
  | nil => exact present
  | cons past edge earlier =>
      obtain ⟨schema, _installed, inputs, _computed, authority⟩ := licensed.2
      rw [edge.physical_result] at present
      rcases mem_fire.mp present with kept | made
      · exact earlier licensed.1 kept.1
      · have allowed := authority.physical.made occurrence made
        change process.rights (location occurrence) .send = true at allowed
        rw [denied] at allowed
        cases allowed

theorem licensed_path_preserves_without_receive
    (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N))
    {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target)
    (licensed : LicensedPath (activate := activate) process location sites path)
    (occurrence : O) (denied : process.rights (location occurrence) .receive = false)
    (present : occurrence ∈ source.inventory.configuration.present) :
    occurrence ∈ target.inventory.configuration.present := by
  induction path with
  | nil => exact present
  | cons past edge earlier =>
      obtain ⟨schema, _installed, inputs, _computed, authority⟩ := licensed.2
      have retained := earlier licensed.1
      rw [edge.physical_result]
      apply mem_fire.mpr
      refine Or.inl ⟨retained, ?_⟩
      intro taken
      have allowed := authority.physical.taken occurrence taken
      change process.rights (location occurrence) .receive = true at allowed
      rw [denied] at allowed
      cases allowed

theorem licensed_edge_requires_peek
    (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N))
    {source target : Endpoint locals O Γ sort} (edge : Firing locals source target)
    (licensed : EdgeLicensed (activate := activate) process location sites edge)
    {occurrence : O} (selected : occurrence ∈ edge.selection.read) :
    process.rights (location occurrence) .peek = true := by
  obtain ⟨schema, _installed, inputs, _computed, authority⟩ := licensed
  exact authority.physical.kept occurrence (by simpa only [Selection.commit, List.mem_toFinset] using selected)

theorem licensed_edge_requires_observe
    (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N))
    {source target : Endpoint locals O Γ sort} (edge : Firing locals source target)
    (licensed : EdgeLicensed (activate := activate) process location sites edge) :
    ∃ schema ∈ process.schemas, ∃ inputs,
      activate source schema inputs = some edge.rule ∧
      ∀ check ∈ (ContextualActivatedStep.prepared locals source.declarations source.occupied edge.selection
          edge.rule source.inventory.rows).rule.checks,
        ContextualSituatedFormation.Regional check → ∀ site ∈ sites source schema inputs check,
          process.rights site .observe = true := by
  obtain ⟨schema, installed, inputs, computed, authority⟩ := licensed
  exact ⟨schema, installed, inputs, computed, authority.regions⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotion
