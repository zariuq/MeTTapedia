import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Coexistence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsTensor

/-! # The existing first-order configuration tensor is the common-frame instance -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence

universe uT uS uOcc
variable {T : Type uT} {S : Type uS} {O : Type uOcc} [DecidableEq O]

theorem annotated_tensor (left right : Configuration T O) :
    tensor left right =
      AnnotatedRuns.tensor left right := rfl

omit [DecidableEq O] in
theorem annotated_unit : unit (T := T) (O := O) =
    AnnotatedRuns.unitConfiguration := rfl

theorem annotated_solutions (A : SubstitutionAction T S) (σ : S)
    (left right : Configuration T O) :
    (Frames.ofSubstitution A).Models (a := PUnit.unit) (b := PUnit.unit) σ
      (tensor left right).equations ↔ A.Models σ left.equations ∧ A.Models σ right.equations := by
  rw [models_tensor]
  exact and_congr (Frames.ofSubstitution_models_iff A σ left.equations)
    (Frames.ofSubstitution_models_iff A σ right.equations)

def annotatedPlacement (A : SubstitutionAction T S) (label : O → T)
    (left right : Configuration T O) :
    EffectCore.Systems.Placement (AnnotatedRuns.firstOrder A label).toStep.effectCore
      [left, right] PUnit.unit := fun _ _ => A.identity

/-- Actual complete first-order states realize to the existing tensor. -/
theorem annotated_realization (A : SubstitutionAction T S) (label : O → T)
    (left right : Configuration T O) :
    EffectCore.Systems.realize (AnnotatedRuns.firstOrder A label).toStep.effectCore
      [left, right] (annotatedPlacement A label left right) = AnnotatedRuns.tensor left right := by
  change tensor
    (transport (Frames.ofSubstitution A) ((Frames.ofSubstitution A).id PUnit.unit) left)
    (tensor (transport (Frames.ofSubstitution A) ((Frames.ofSubstitution A).id PUnit.unit) right)
      unit) = _
  rw [transport_id, transport_id, tensor_unit, annotated_tensor]

/-- A family shares one substitution at the common frame, exactly as the old tensor does. -/
theorem annotated_joint_solvable (A : SubstitutionAction T S) (label : O → T)
    (left right : Configuration T O) :
    EffectCore.Systems.NativeSolvable (AnnotatedRuns.firstOrder A label).toStep.effectCore [left, right] ↔
      A.Consistent (AnnotatedRuns.tensor left right).equations := by
  constructor
  · rintro ⟨target, placement, solved⟩
    cases target
    let σ := placement PUnit.unit (by simp [AnnotatedRuns.firstOrder])
    have one := solved left (by simp)
    have two := solved right (by simp)
    change (Frames.ofSubstitution A).Models (a := PUnit.unit) (b := PUnit.unit) σ left.equations at one
    change (Frames.ofSubstitution A).Models (a := PUnit.unit) (b := PUnit.unit) σ right.equations at two
    refine ⟨σ, (A.models_append σ left.equations right.equations).mpr ?_⟩
    exact ⟨(Frames.ofSubstitution_models_iff A σ left.equations).mp one,
      (Frames.ofSubstitution_models_iff A σ right.equations).mp two⟩
  · rintro ⟨σ, solved⟩
    have both := (A.models_append σ left.equations right.equations).mp solved
    refine ⟨PUnit.unit, (fun _ _ => σ), ?_⟩
    intro state member
    rcases List.mem_cons.mp member with same | later
    · subst state
      exact (Frames.ofSubstitution_models_iff A σ left.equations).mpr both.1
    · have same := List.mem_singleton.mp later
      subst state
      exact (Frames.ofSubstitution_models_iff A σ right.equations).mpr both.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence
