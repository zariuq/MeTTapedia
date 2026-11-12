import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FramedNative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceControls

/-! # Joint family-frame configurations and their native controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.FramedConfiguration.Controls

open Coexistence.Controls (discreteFrames DiscreteHom no_common_native_frame)

def leftNative : Configuration Bool Nat := ⟨[(false, false)], {0}⟩
def rightNative : Configuration Bool Nat := ⟨[(true, true)], {1}⟩
def left := ofNative (Tm := fun _ : Bool => Bool) false leftNative
def right := ofNative (Tm := fun _ : Bool => Bool) true rightNative
def joint := tensor left right

theorem family_of_joint : joint.frames = [false, true] := rfl

theorem occurrences_of_joint : joint.content.present = ({0, 1} : Finset Nat) := by decide

/-- Both original components have solutions, without a common original target. -/
theorem original_components_solvable :
    discreteFrames.Solvable (a := false) leftNative.equations ∧
      discreteFrames.Solvable (a := true) rightNative.equations := by
  constructor
  · refine ⟨false, discreteFrames.id false, ?_⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · refine ⟨true, discreteFrames.id true, ?_⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl

theorem joint_has_family_solution : discreteFrames.families.Solvable joint.content.equations := by
  refine ⟨joint.frames, discreteFrames.families.id _, ?_⟩
  apply (models_tensor discreteFrames left right _).mpr
  constructor
  · apply (models_ofNative discreteFrames false leftNative _).mpr
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · apply (models_ofNative discreteFrames true rightNative _).mpr
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl

theorem native_apex_not_required :
    (¬∃ target : Bool, Nonempty (DiscreteHom false target) ∧ Nonempty (DiscreteHom true target)) ∧
      discreteFrames.families.Solvable joint.content.equations :=
  ⟨no_common_native_frame, joint_has_family_solution⟩

open AdmissionObservationCover.Controls (frame)
open Coexistence.Controls (zero one individually_solvable_jointly_inconsistent)

theorem shared_frame_preserves_joint_inconsistency :
    ¬frame.families.Solvable (tensor (ofNative () zero) (ofNative () one)).content.equations := by
  intro solved
  exact individually_solvable_jointly_inconsistent.2.2
    ((joint_native_solvable_iff frame () zero one).mp solved)

def emptyFrameUnit : FramedConfiguration (fun _ : Empty => Bool) Nat := unit

theorem empty_frame_unit_exists : emptyFrameUnit.frames = [] ∧ emptyFrameUnit.content.present = ∅ :=
  ⟨rfl, rfl⟩

theorem empty_frame_unit_has_no_phantom_term :
    ¬Nonempty (Frames.Families.Term (fun _ : Empty => Bool) emptyFrameUnit.frames) :=
  Frames.Families.empty_term_fibre (Tm := fun _ : Empty => Bool)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.FramedConfiguration.Controls
