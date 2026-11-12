import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FramedNative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FrameIndexing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceControls

/-! # Context copies and shared declarations have different joint solutions -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.FramedConfiguration.ScopeControls

open AdmissionObservationCover.Controls (frame World)
open Coexistence.Controls (zero one individually_solvable_jointly_inconsistent)

abbrev copiedFrames := frame.copies Bool
def first := ofNative (Tm := fun _ : Bool × Unit => World → Bool) (false, ()) zero
def second := ofNative (Tm := fun _ : Bool × Unit => World → Bool) (true, ()) one
def joint := tensor first second

def independentMap : Frames.Families.Map (fun _ _ : Bool × Unit => World → World)
    joint.frames joint.frames :=
  fun source member => ⟨⟨source, member⟩, fun _ _ => source.1⟩

theorem copied_contexts_jointly_solvable : copiedFrames.families.Solvable joint.content.equations := by
  refine ⟨joint.frames, independentMap, ?_⟩
  apply (models_tensor copiedFrames first second _).mpr
  constructor
  · apply (models_ofNative copiedFrames (false, ()) zero _).mpr
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · apply (models_ofNative copiedFrames (true, ()) one _).mpr
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl

theorem shared_contexts_jointly_inconsistent :
    ¬frame.families.Solvable (tensor (ofNative () zero) (ofNative () one)).content.equations := by
  intro solved
  exact individually_solvable_jointly_inconsistent.2.2
    ((joint_native_solvable_iff frame () zero one).mp solved)

/-- Forgetting which frame copy is used changes the joint solvability question. -/
theorem copy_identity_matters :
    copiedFrames.families.Solvable joint.content.equations ∧
      ¬frame.families.Solvable (tensor (ofNative () zero) (ofNative () one)).content.equations :=
  ⟨copied_contexts_jointly_solvable, shared_contexts_jointly_inconsistent⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.FramedConfiguration.ScopeControls
