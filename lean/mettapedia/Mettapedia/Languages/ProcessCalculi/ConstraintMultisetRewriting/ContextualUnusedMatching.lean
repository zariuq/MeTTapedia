import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnusedExtensions

/-!
# Schema and shared-row matches reflect unused-frame extension

Schema witnesses are joined with the unused declarations through the actual
constructed extension square. Restriction preserves their captured images.
Live matches use the proved injectivity of the capture inclusion. Private
locals and shared captures keep their original distinct roles.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPrefixModels

variable {S : Signature} {Extra Local Shared Next : Type}
  (locals : Local → MetaArity S) (unused : Extra → MetaArity S)
  {captures : Shared → MetaArity S} {next : Next → MetaArity S}

theorem instance_add_unused (extension : Extension next)
    (localBodies : Assignment locals extension.declarations) (candidate : Assignment captures next) :
    Assignment.compose (inclusion unused extension.declarations)
        (instanceAssignment locals localBodies extension.assignment candidate) =
      instanceAssignment locals (Assignment.compose (inclusion unused extension.declarations) localBodies)
        (extension.addUnused unused).assignment (Assignment.compose (inclusion unused next) candidate) := by
  funext name
  cases name with
  | inl name => rfl
  | inr name =>
      change instantiate (inclusion unused extension.declarations)
          (instantiate extension.assignment (candidate name)) =
        instantiate (extension.addUnused unused).assignment (instantiate (inclusion unused next) (candidate name))
      rw [Extension.addUnused_assignment]
      exact (ContextualStoredRows.liftCaptures_on_shared_value unused extension.assignment (candidate name)).symm

theorem instance_restrict_unused (extension : Extension (extended unused next))
    (localBodies : Assignment locals extension.declarations) (candidate : Assignment captures next) :
    instanceAssignment locals localBodies extension.assignment
        (Assignment.compose (inclusion unused next) candidate) =
      instanceAssignment locals localBodies (extension.restrictUnused unused).assignment candidate := by
  funext name
  cases name with
  | inl name => rfl
  | inr name =>
      change instantiate extension.assignment (instantiate (inclusion unused next) (candidate name)) =
        instantiate (extension.restrictUnused unused).assignment (candidate name)
      rw [← Assignment.instantiate_compose, ← Extension.restrictUnused_assignment]
      rfl

theorem matches_inclusion_iff (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (pattern : Term (signature S next) Γ sort)
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    Matches locals (Assignment.compose (inclusion unused next) candidate)
        (instantiate (inclusion unused next) pattern) row ↔
      Matches locals candidate pattern row := by
  cases row with
  | shared value =>
      change (instantiate (inclusion unused next) pattern =
        instantiate (Assignment.compose (inclusion unused next) candidate) value) ↔
          pattern = instantiate candidate value
      rw [Assignment.instantiate_compose]
      exact ⟨fun same => inclusion_injective unused next _ _ same,
        congrArg (instantiate (inclusion unused next))⟩
  | schema body =>
      constructor
      · rintro ⟨extension, localBodies, agrees⟩
        refine ⟨extension.restrictUnused unused, localBodies, ?_⟩
        rw [instance_restrict_unused] at agrees
        have right : instantiate extension.assignment (instantiate (inclusion unused next) pattern) =
            instantiate (extension.restrictUnused unused).assignment pattern := by
          rw [← Assignment.instantiate_compose, ← Extension.restrictUnused_assignment]
          rfl
        exact agrees.trans right
      · rintro ⟨extension, localBodies, agrees⟩
        refine ⟨extension.addUnused unused, Assignment.compose (inclusion unused extension.declarations) localBodies, ?_⟩
        change instantiate (instanceAssignment locals
          (Assignment.compose (inclusion unused extension.declarations) localBodies)
          (extension.addUnused unused).assignment (Assignment.compose (inclusion unused next) candidate)) body =
            instantiate (extension.addUnused unused).assignment (instantiate (inclusion unused next) pattern)
        have left := congrArg
          (fun assignment : Assignment (ContextualSelectionViews.source locals captures)
              (extended unused extension.declarations) => instantiate assignment body)
          (instance_add_unused locals unused extension localBodies candidate)
        simp only [Assignment.instantiate_compose] at left
        have mapped := congrArg (instantiate (inclusion unused extension.declarations)) agrees
        have right : instantiate (inclusion unused extension.declarations)
            (instantiate extension.assignment pattern) =
              instantiate (extension.addUnused unused).assignment (instantiate (inclusion unused next) pattern) := by
          rw [Extension.addUnused_assignment]
          exact (ContextualStoredRows.liftCaptures_on_shared_value unused extension.assignment pattern).symm
        exact left.symm.trans (mapped.trans right)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching
